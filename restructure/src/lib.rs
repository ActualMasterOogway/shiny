use ast::{LocalRw, Traverse};
use cfg::{block::BranchType, function::Function};
use itertools::Itertools;
use parking_lot::Mutex;
use triomphe::Arc;
use rustc_hash::{FxHashMap, FxHashSet};

use petgraph::{
    algo::dominators::{simple_fast, Dominators},
    stable_graph::{EdgeIndex, NodeIndex, StableDiGraph},
    visit::*,
};
use tuple::Map;

mod conditional;
mod jump;
mod r#loop;

// TODO: REFACTOR: move
pub fn post_dominators<N: Default, E: Default>(
    graph: &mut StableDiGraph<N, E>,
) -> Dominators<NodeIndex> {
    let exits = graph
        .node_identifiers()
        .filter(|&n| graph.neighbors(n).count() == 0)
        .collect_vec();
    let fake_exit = graph.add_node(Default::default());
    for exit in exits {
        graph.add_edge(exit, fake_exit, Default::default());
    }
    let res = simple_fast(Reversed(&*graph), fake_exit);
    assert!(graph.remove_node(fake_exit).is_some());
    res
}

struct GraphStructurer {
    pub function: Function,
    loop_headers: FxHashSet<NodeIndex>,
    label_to_node: FxHashMap<ast::Label, NodeIndex>,
}

impl GraphStructurer {
    fn find_loop_headers(&mut self) {
        self.loop_headers.clear();
        depth_first_search(
            self.function.graph(),
            Some(self.function.entry().unwrap()),
            |event| {
                if let DfsEvent::BackEdge(_, header) = event {
                    self.loop_headers.insert(header);
                }
            },
        );
    }
    fn new(function: Function) -> Self {
        let mut this = Self {
            function,
            loop_headers: FxHashSet::default(),
            label_to_node: FxHashMap::default(),
        };
        this.find_loop_headers();
        this
    }

    fn block_is_no_op(block: &ast::Block) -> bool {
        !block.iter().any(|s| s.as_comment().is_none())
    }

    fn try_match_pattern(
        &mut self,
        node: NodeIndex,
        dominators: &Dominators<NodeIndex>,
        post_dom: &Dominators<NodeIndex>,
    ) -> bool {
        let successors = self.function.successor_blocks(node).collect_vec();

        // cfg::dot::render_to(&self.function, &mut std::io::stdout()).unwrap();
        if self.try_collapse_loop(node, dominators, post_dom) {
            self.find_loop_headers();
            // println!("matched loop");
            return true;
        }

        if self.try_remove_unnecessary_condition(node) {
            return true;
        }

        let changed = match successors.len() {
            0 => false,
            1 => {
                // remove unnecessary jumps to allow pattern matching
                self.match_jump(node, Some(successors[0]))
            }
            2 => {
                let (then_target, else_target) = self
                    .function
                    .conditional_edges(node)
                    .unwrap()
                    .map(|e| e.target());
                self.match_inner_loop_continue(node, then_target, else_target, dominators)
                    || self.match_conditional(node, then_target, else_target)
            }

            _ => unreachable!(),
        };

        //println!("after");
        //dot::render_to(&self.function, &mut std::io::stdout()).unwrap();

        changed
    }

    fn match_blocks(&mut self) -> bool {
        let dfs = Dfs::new(self.function.graph(), self.function.entry().unwrap())
            .iter(self.function.graph())
            .collect::<FxHashSet<_>>();
        let mut dfs_postorder =
            DfsPostOrder::new(self.function.graph(), self.function.entry().unwrap());
        let mut dominators = simple_fast(self.function.graph(), self.function.entry().unwrap());
        let mut post_dom = post_dominators(self.function.graph_mut());

        // cfg::dot::render_to(&self.function, &mut std::io::stdout()).unwrap();

        let mut changed = false;
        while let Some(node) = dfs_postorder.next(self.function.graph()) {
            // println!("matching {:?}", node);
            let matched = self.try_match_pattern(node, &dominators, &post_dom);
            if matched {
                dominators = simple_fast(self.function.graph(), self.function.entry().unwrap());
                post_dom = post_dominators(self.function.graph_mut());
            }
            changed |= matched;
            // if matched {
            //     cfg::dot::render_to(&self.function, &mut std::io::stdout()).unwrap();
            // }
        }

        for node in self
            .function
            .graph()
            .node_indices()
            .filter(|node| !dfs.contains(node))
            .collect_vec()
        {
            // block may have been removed in a previous iteration
            if self.function.has_block(node)
                && self.function.predecessor_blocks(node).next().is_none()
            {
                if self
                    .function
                    .block(node)
                    .unwrap()
                    .first()
                    .and_then(|s| s.as_label())
                    .is_none()
                {
                    self.function.remove_block(node);
                } else {
                    //let dominators = simple_fast(self.function.graph(), node);
                    let matched = self.try_match_pattern(node, &dominators, &post_dom);
                    changed |= matched;
                }
            }
        }

        changed
    }

    fn insert_goto_for_edge(&mut self, edge: EdgeIndex) {
        let (source, target) = self.function.graph().edge_endpoints(edge).unwrap();
        if self.function.graph().edge_weight(edge).unwrap().branch_type == BranchType::Unconditional
            && self.function.predecessor_blocks(target).count() == 1
        {
            assert!(self.function.successor_blocks(source).count() == 1);
            // TODO: this code is repeated in match_jump, move to a new function
            let edges = self.function.remove_edges(target);
            let block = self.function.remove_block(target).unwrap();
            self.function.block_mut(source).unwrap().extend(block.0);
            self.function.set_edges(source, edges);
        } else if let Some(terminator) = Self::cheap_terminator(self.function.block(target).unwrap())
        {
            // luau has no goto, so copy the terminator to every fan-in instead
            let goto_block = self.function.new_block();
            self.function
                .block_mut(goto_block)
                .unwrap()
                .push(terminator);
            let edge = self.function.graph_mut().remove_edge(edge).unwrap();
            self.function.graph_mut().add_edge(source, goto_block, edge);
        } else {
            // TODO: make label an Rc and have a global counter for block name
            let label = ast::Label(format!("l{}", target.index()));
            let target_block = self.function.block_mut(target).unwrap();
            if target_block.first().and_then(|s| s.as_label()).is_none() {
                self.label_to_node.insert(label.clone(), target);
                target_block.insert(0, label.clone().into());
            }
            let goto_block = self.function.new_block();
            self.function
                .block_mut(goto_block)
                .unwrap()
                .push(ast::Goto::new(label).into());

            let edge = self.function.graph_mut().remove_edge(edge).unwrap();
            self.function.graph_mut().add_edge(source, goto_block, edge);
        }
    }

    // a goto to a block thats only a terminator can just be the terminator
    fn cheap_terminator(block: &ast::Block) -> Option<ast::Statement> {
        let stmts: Vec<&ast::Statement> = block
            .iter()
            .filter(|s| !matches!(s, ast::Statement::Label(_)))
            .collect();
        let [only] = stmts.as_slice() else {
            return None;
        };
        match only {
            ast::Statement::Return(r) if r.values.is_empty() => {
                Some(ast::Return::new(Vec::new()).into())
            }
            ast::Statement::Break(_) => Some(ast::Break {}.into()),
            ast::Statement::Continue(_) => Some(ast::Continue {}.into()),
            _ => None,
        }
    }

    fn remove_last_return(block: ast::Block) -> ast::Block {
        if let Some(ast::Statement::Return(last_statement)) = block.last() {
            if last_statement.values.is_empty() {
                let take = block.len() - 1;
                return block.0.into_iter().take(take).collect_vec().into();
            }
        }
        block
    }

    // bigger bloats the output, smaller misses real opportunities
    const TAIL_DUPLICATION_LIMIT: usize = 8;

    // a shallow clone shares the if/loop body arcs, and the passes after this
    // mutate them in place, which corrupts both copies
    fn deep_clone_block(block: &ast::Block) -> ast::Block {
        let mut cloned = block.clone();
        for stmt in cloned.iter_mut() {
            match stmt {
                ast::Statement::If(s) => {
                    let t = Self::deep_clone_block(&s.then_block.lock());
                    s.then_block = Arc::new(Mutex::new(t));
                    let e = Self::deep_clone_block(&s.else_block.lock());
                    s.else_block = Arc::new(Mutex::new(e));
                }
                ast::Statement::While(s) => {
                    let b = Self::deep_clone_block(&s.block.lock());
                    s.block = Arc::new(Mutex::new(b));
                }
                ast::Statement::Repeat(s) => {
                    let b = Self::deep_clone_block(&s.block.lock());
                    s.block = Arc::new(Mutex::new(b));
                }
                ast::Statement::NumericFor(s) => {
                    let b = Self::deep_clone_block(&s.block.lock());
                    s.block = Arc::new(Mutex::new(b));
                }
                ast::Statement::GenericFor(s) => {
                    let b = Self::deep_clone_block(&s.block.lock());
                    s.block = Arc::new(Mutex::new(b));
                }
                _ => {}
            }
        }
        cloned
    }

    // a closures function arc is keyed by identity in the upvalue-link map, so
    // sharing it double-links and cloning it loses the key. dont duplicate those
    fn block_has_closure(block: &ast::Block) -> bool {
        let mut tmp = block.clone();
        for stmt in tmp.iter_mut() {
            let mut found = false;
            stmt.traverse_rvalues(&mut |r| {
                if matches!(r, ast::RValue::Closure(_)) {
                    found = true;
                }
            });
            if found {
                return true;
            }
            let sub = match stmt {
                ast::Statement::If(s) => {
                    Self::block_has_closure(&s.then_block.lock())
                        || Self::block_has_closure(&s.else_block.lock())
                }
                ast::Statement::While(s) => Self::block_has_closure(&s.block.lock()),
                ast::Statement::Repeat(s) => Self::block_has_closure(&s.block.lock()),
                ast::Statement::NumericFor(s) => Self::block_has_closure(&s.block.lock()),
                ast::Statement::GenericFor(s) => Self::block_has_closure(&s.block.lock()),
                _ => false,
            };
            if sub {
                return true;
            }
        }
        false
    }

    // clone fan-in blocks so every copy has one predecessor, which is what the
    // diamond/triangle/jump matchers need. only run after they reach a fixed point
    // so we dont duplicate something they could have collapsed on their own
    fn tail_duplicate(&mut self) -> bool {
        let entry = self.function.entry().unwrap();
        let candidates: Vec<NodeIndex> = self
            .function
            .graph()
            .node_indices()
            .filter(|&n| n != entry)
            .filter(|&n| !self.is_loop_header(n))
            .filter(|&n| {
                let block = self.function.block(n).unwrap();
                if block.is_empty() {
                    return false;
                }
                // a join that only leads to a return is bounded, so allow bigger
                // ones there
                let is_tail = self.function.successor_blocks(n).count() == 0
                    || self
                        .function
                        .successor_blocks(n)
                        .all(|s| self.function.successor_blocks(s).count() == 0);
                let limit = if is_tail {
                    Self::TAIL_DUPLICATION_LIMIT * 4
                } else {
                    Self::TAIL_DUPLICATION_LIMIT
                };
                if block.len() > limit {
                    return false;
                }
                if matches!(block.first(), Some(ast::Statement::Label(_))) {
                    return false;
                }
                // a collapsed loop statement is self-contained and safe to copy,
                // only the for-init/for-next pseudo-statements pair with a header
                block.iter().all(|s| {
                    !matches!(
                        s,
                        ast::Statement::NumForInit(_)
                            | ast::Statement::NumForNext(_)
                            | ast::Statement::GenericForInit(_)
                            | ast::Statement::GenericForNext(_)
                    )
                }) && !Self::block_has_closure(block)
            })
            .filter(|&n| {
                let preds: Vec<_> = self
                    .function
                    .predecessor_blocks(n)
                    .filter(|&p| p != n)
                    .collect();
                preds.len() >= 2
            })
            .collect();
        if candidates.is_empty() {
            return false;
        }
        let mut duplicated = false;
        for node in candidates {
            // earlier iterations may have changed these
            let incoming: Vec<EdgeIndex> = self
                .function
                .graph()
                .edges_directed(node, petgraph::Direction::Incoming)
                .map(|e| e.id())
                .collect();
            if incoming.len() < 2 {
                continue;
            }
            let block_template = self.function.block(node).unwrap().clone();
            let outgoing: Vec<(NodeIndex, cfg::block::BlockEdge)> = self
                .function
                .graph()
                .edges_directed(node, petgraph::Direction::Outgoing)
                .map(|e| (e.target(), e.weight().clone()))
                .collect();
            // first predecessor keeps the original, the rest get clones
            for &edge in incoming.iter().skip(1) {
                let Some((source, _)) = self.function.graph().edge_endpoints(edge) else {
                    continue;
                };
                let edge_weight = self
                    .function
                    .graph()
                    .edge_weight(edge)
                    .cloned()
                    .unwrap_or_default();
                let clone = self.function.new_block();
                *self.function.block_mut(clone).unwrap() = Self::deep_clone_block(&block_template);
                for (target, weight) in &outgoing {
                    self.function
                        .graph_mut()
                        .add_edge(clone, *target, weight.clone());
                }
                self.function.graph_mut().remove_edge(edge);
                self.function
                    .graph_mut()
                    .add_edge(source, clone, edge_weight);
                duplicated = true;
            }
        }
        if duplicated {
            self.find_loop_headers();
        }
        duplicated
    }

    // a break/continue not inside a loop here belongs to an enclosing loop, and
    // the dispatch `while true` would steal it
    fn block_has_dangling_break_continue(block: &ast::Block) -> bool {
        block.iter().any(|stmt| match stmt {
            ast::Statement::Break(_) | ast::Statement::Continue(_) => true,
            ast::Statement::If(s) => {
                Self::block_has_dangling_break_continue(&s.then_block.lock())
                    || Self::block_has_dangling_break_continue(&s.else_block.lock())
            }
            _ => false,
        })
    }

    // same skip rule as LocalDeclarer, a for's induction variable is per-iteration
    // and must not be hoisted out of the loop, so only recurse into its body
    fn collect_residual_writes(block: &ast::Block, out: &mut FxHashSet<ast::RcLocal>) {
        for stat in block.iter() {
            match stat {
                ast::Statement::NumericFor(s) => {
                    Self::collect_residual_writes(&s.block.lock(), out);
                }
                ast::Statement::GenericFor(s) => {
                    Self::collect_residual_writes(&s.block.lock(), out);
                }
                ast::Statement::If(s) => {
                    for local in stat.values_written() {
                        out.insert(local.clone());
                    }
                    Self::collect_residual_writes(&s.then_block.lock(), out);
                    Self::collect_residual_writes(&s.else_block.lock(), out);
                }
                ast::Statement::While(s) => {
                    for local in stat.values_written() {
                        out.insert(local.clone());
                    }
                    Self::collect_residual_writes(&s.block.lock(), out);
                }
                ast::Statement::Repeat(s) => {
                    for local in stat.values_written() {
                        out.insert(local.clone());
                    }
                    Self::collect_residual_writes(&s.block.lock(), out);
                }
                other => {
                    for local in other.values_written() {
                        out.insert(local.clone());
                    }
                }
            }
        }
    }

    // flatten the whole residual into `local state = n; while true do if state == 1
    // then ... elseif ... end end`. always runnable, but the output is ugly
    // TODO: this fires for reducible residuals too, which is overkill. a reducible
    // region can always be done with a guard boolean instead, no duplication and no
    // state machine. only irreducible cfgs actually need this
    fn dispatch_residual(&mut self) -> bool {
        let nodes: Vec<NodeIndex> = self.function.graph().node_indices().collect();
        if nodes.iter().any(|&n| {
            self.is_loop_header(n)
                || Self::block_has_dangling_break_continue(self.function.block(n).unwrap())
        }) {
            return false;
        }
        let entry = self.function.entry().unwrap();
        let id: FxHashMap<NodeIndex, usize> =
            nodes.iter().enumerate().map(|(i, &n)| (n, i + 1)).collect();
        debug_assert!(self
            .function
            .graph()
            .edge_indices()
            .all(|e| id.contains_key(&self.function.graph().edge_endpoints(e).unwrap().1)));

        let state_local = ast::RcLocal::default();

        // the arms are siblings, so LocalDeclarer would park each `local` inside the
        // one arm that writes it and reads from the others would hit a nil global.
        // a bare decl at the root dominates every arm
        let mut hoist_locals: FxHashSet<ast::RcLocal> = FxHashSet::default();
        for &n in &nodes {
            Self::collect_residual_writes(
                self.function.block(n).unwrap(),
                &mut hoist_locals,
            );
        }

        // while the graph is still intact
        let mut arms: Vec<(usize, ast::Block)> = Vec::new();
        for &n in &nodes {
            let mut body = self.function.block(n).unwrap().clone();
            let succs: Vec<NodeIndex> = self.function.successor_blocks(n).collect();
            match succs.len() {
                0 => {
                    if !matches!(body.last(), Some(ast::Statement::Return(_))) {
                        body.push(ast::Break {}.into());
                    }
                }
                1 => {
                    body.push(
                        ast::Assign::new(
                            vec![ast::LValue::Local(state_local.clone())],
                            vec![ast::Literal::Number(id[&succs[0]] as f64).into()],
                        )
                        .into(),
                    );
                }
                2 => {
                    let (then_e, else_e) = self.function.conditional_edges(n).unwrap();
                    let (t, e) = (id[&then_e.target()], id[&else_e.target()]);
                    let Ok(if_stat) = body.pop().unwrap().into_if() else {
                        return false;
                    };
                    body.push(
                        ast::If::new(
                            if_stat.condition,
                            vec![ast::Assign::new(
                                vec![ast::LValue::Local(state_local.clone())],
                                vec![ast::Literal::Number(t as f64).into()],
                            )
                            .into()]
                            .into(),
                            vec![ast::Assign::new(
                                vec![ast::LValue::Local(state_local.clone())],
                                vec![ast::Literal::Number(e as f64).into()],
                            )
                            .into()]
                            .into(),
                        )
                        .into(),
                    );
                }
                _ => unreachable!(),
            }
            arms.push((id[&n], body));
        }

        let (_, mut acc) = arms.pop().unwrap();
        while let Some((k, arm)) = arms.pop() {
            let cond = ast::Binary::new(
                ast::RValue::Local(state_local.clone()),
                ast::Literal::Number(k as f64).into(),
                ast::BinaryOperation::Equal,
            )
            .into();
            acc = vec![ast::Statement::from(ast::If::new(cond, arm, acc))].into();
        }

        let mut out_body = ast::Block::default();
        out_body.push(ast::Comment::new("control flow flattened: this region could not be structured without a
            `goto` (unsupported in Luau), so it was lowered to the state-machine
            dispatch loop below to keep the output runnable.".to_string()).into());
        if !hoist_locals.is_empty() {
            let mut hoist = ast::Assign::new(
                hoist_locals
                    .into_iter()
                    .map(ast::LValue::Local)
                    .collect(),
                Vec::new(),
            );
            hoist.prefix = true;
            out_body.push(hoist.into());
        }
        let mut init = ast::Assign::new(
            vec![ast::LValue::Local(state_local.clone())],
            vec![ast::Literal::Number(id[&entry] as f64).into()],
        );
        init.prefix = true;
        out_body.push(init.into());
        out_body
            .push(ast::While::new(ast::Literal::Boolean(true).into(), acc).into());

        for &n in &nodes {
            self.function.remove_block(n);
        }
        let out = self.function.new_block();
        *self.function.block_mut(out).unwrap() = out_body;
        self.function.set_entry(out);
        true
    }

    fn collapse(&mut self) {
        let mut taildup_rounds = 0u32;
        loop {
            while self.match_blocks() {}
            if self.function.graph().node_count() == 1 {
                break;
            }
            // duplicating one join exposes the next, so keep going while it shrinks
            let before = self.function.graph().node_count();
            if taildup_rounds < 16 && self.tail_duplicate() {
                taildup_rounds += 1;
                while self.match_blocks() {}
                if self.function.graph().node_count() == 1 {
                    break;
                }
                if self.function.graph().node_count() < before {
                    continue;
                }
            }
            // otherwise fall through to the goto refinement below
            if self.dispatch_residual() {
                break;
            }
            // last resort refinement
            let edges = self.function.graph().edge_indices().collect::<Vec<_>>();
            // https://edmcman.github.io/papers/usenix13.pdf
            // we prefer to remove edges whose source does not dominate its target, nor whose target dominates its source
            // TODO: try all possible paths and return the one with the least gotos, i don't think there's any other way
            // to get best output
            let mut changed = false;
            for &edge in &edges {
                // edge might have been invalidated by a previous iteration due to insert_goto_for_edge
                // calling remove_block(target)
                if self.function.graph().edge_weight(edge).is_none() {
                    continue;
                }

                let (source, target) = self.function.graph().edge_endpoints(edge).unwrap();
                let dominators = simple_fast(self.function.graph(), self.function.entry().unwrap());
                let target_dominators = dominators.dominators(target);
                let source_dominators = dominators.dominators(source);
                // TODO: check if blocks in dfs instead
                if target_dominators.is_none() || source_dominators.is_none() {
                    continue;
                }
                let mut target_dominators = target_dominators.unwrap();
                let mut source_dominators = source_dominators.unwrap();
                if target_dominators.contains(&source) || source_dominators.contains(&target) {
                    continue;
                }

                self.insert_goto_for_edge(edge);
                self.find_loop_headers();
                changed = self.match_blocks();
                if changed {
                    break;
                }
            }

            if !changed {
                for edge in edges {
                    // edge might have been invalidated by a previous iteration due to insert_goto_for_edge
                    // calling remove_block(target)
                    if self.function.graph().edge_weight(edge).is_none() {
                        continue;
                    }
                    self.insert_goto_for_edge(edge);
                    self.find_loop_headers();
                    changed = self.match_blocks();
                    if changed {
                        break;
                    }
                }
                if !changed {
                    break;
                }
            }
        }
    }

    fn structure(mut self) -> ast::Block {
        self.collapse();
        if self.function.graph().node_count() != 1 {
            let mut res_block = ast::Block::default();
            let entry = self.function.entry().unwrap();
            let mut stack = vec![entry];
            let mut visited = FxHashSet::default();
            while let Some(node) = stack.pop() {
                if visited.contains(&node) {
                    continue;
                }
                visited.insert(node);

                fn collect_gotos(block: &ast::Block, gotos: &mut FxHashSet<ast::Label>) {
                    for statement in &block.0 {
                        match statement {
                            ast::Statement::Goto(goto) => {
                                gotos.insert(goto.0.clone());
                            }
                            ast::Statement::If(r#if) => {
                                collect_gotos(&r#if.then_block.lock(), gotos);
                                collect_gotos(&r#if.else_block.lock(), gotos);
                            }
                            ast::Statement::While(r#while) => {
                                collect_gotos(&r#while.block.lock(), gotos);
                            }
                            ast::Statement::Repeat(repeat) => {
                                collect_gotos(&repeat.block.lock(), gotos);
                            }
                            ast::Statement::NumericFor(numeric_for) => {
                                collect_gotos(&numeric_for.block.lock(), gotos);
                            }
                            ast::Statement::GenericFor(generic_for) => {
                                collect_gotos(&generic_for.block.lock(), gotos);
                            }
                            _ => {}
                        }
                    }
                }

                let block = self.function.remove_block(node).unwrap();
                let mut goto_destinations = FxHashSet::default();
                collect_gotos(&block, &mut goto_destinations);
                for label in goto_destinations {
                    // TODO: block might have been merged/structured into another, output that block instead
                    // will require collecting label definitions in addition to references (gotos)
                    let target_node = self.label_to_node[&label];
                    if self.function.has_block(target_node) {
                        stack.push(target_node);
                    }
                }
                if let Some(ast::Statement::Goto(goto)) = res_block.last()
                // TODO: keep label -> block map instead
                    && goto.0.0[1..] == node.index().to_string()
                {
                    res_block.pop();
                }
                if !block
                    .first()
                    .is_some_and(|s| matches!(s, ast::Statement::Label(_)))
                {
                    res_block.push(ast::Comment::new(format!("block {}", node.index())).into());
                }
                res_block.extend(block.0)
            }
            // TODO: these nodes are never executed (i think), comment them out or dont include them
            for node in self.function.graph().node_indices().collect::<Vec<_>>() {
                let block = self.function.remove_block(node).unwrap();
                if !block
                    .first()
                    .is_some_and(|s| matches!(s, ast::Statement::Label(_)))
                {
                    res_block.push(ast::Comment::new(format!("block {}", node.index())).into());
                }
                res_block.extend(block.0)
            }

            res_block
        } else {
            Self::remove_last_return(
                self.function
                    .remove_block(self.function.entry().unwrap())
                    .unwrap(),
            )
        }
    }
}

pub fn lift(function: cfg::function::Function) -> ast::Block {
    GraphStructurer::new(function).structure()
}
