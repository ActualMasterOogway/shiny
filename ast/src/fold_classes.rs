use itertools::Either;

use crate::{Block, ClassMethod, Literal, RValue, RcLocal, Statement, Traverse};

// Matches a `class_local[name] = value` field assignment and returns the field
// name, when the assignment targets the given class local with a string key.
fn method_name(statement: &Statement, class_local: &RcLocal) -> Option<String> {
    let assign = statement.as_assign()?;
    if assign.left.len() != 1 || assign.right.len() != 1 || assign.prefix {
        return None;
    }
    let index = assign.left[0].as_index()?;
    let RValue::Local(target) = index.left.as_ref() else {
        return None;
    };
    if target != class_local {
        return None;
    }
    let RValue::Literal(Literal::String(name)) = index.right.as_ref() else {
        return None;
    };
    Some(String::from_utf8_lossy(name).into_owned())
}

// Folds `class_local.method = closure` assignments emitted after a `class`
// declaration back into the declaration's body. The lifter keeps methods as
// plain assignments so SSA can resolve self referencing methods, this pass
// restores the `class Name ... function m() end ... end` shape for output.
pub fn fold_classes(block: &mut Block) {
    let mut index = 0;
    while index < block.len() {
        if let Some(class_local) = block[index].as_class().map(|c| c.local.clone()) {
            let mut methods = Vec::new();
            while index + 1 < block.len() {
                let Some(name) = method_name(&block[index + 1], &class_local) else {
                    break;
                };
                let assign = block.0.remove(index + 1).into_assign().unwrap();
                let value = assign.right.into_iter().next().unwrap();
                methods.push(ClassMethod { name, value });
            }
            block[index]
                .as_class_mut()
                .unwrap()
                .methods
                .extend(methods);
        }
        index += 1;
    }

    // Recurse into nested blocks and every closure body (including the method
    // closures just folded into class nodes, reached as rvalues).
    for statement in &mut block.0 {
        statement.post_traverse_values(&mut |value| -> Option<()> {
            if let Either::Right(RValue::Closure(closure)) = value {
                fold_classes(&mut closure.function.lock().body);
            }
            None
        });
        match statement {
            Statement::If(r#if) => {
                fold_classes(&mut r#if.then_block.lock());
                fold_classes(&mut r#if.else_block.lock());
            }
            Statement::While(r#while) => fold_classes(&mut r#while.block.lock()),
            Statement::Repeat(repeat) => fold_classes(&mut repeat.block.lock()),
            Statement::NumericFor(numeric_for) => fold_classes(&mut numeric_for.block.lock()),
            Statement::GenericFor(generic_for) => fold_classes(&mut generic_for.block.lock()),
            _ => {}
        }
    }
}
