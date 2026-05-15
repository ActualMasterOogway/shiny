use std::fmt;

use crate::{formatter::Formatter, has_side_effects, LocalRw, RValue, RcLocal, Traverse};

// A method of a `class` declaration. `value` starts life as the temporary local
// that LOP_NEWCLASSMEMBER copies the closure from, and is inlined into the actual
// closure by the SSA inlining pass.
#[derive(Debug, Clone, PartialEq)]
pub struct ClassMethod {
    pub name: String,
    pub value: RValue,
}

// A Luau `class Name ... end` declaration (bytecode v10+, FFlag::DebugLuauUserDefinedClasses).
// `local` is the class object the declaration binds, `name` is the original class
// name carried by the CLASS_SHAPE constant
#[derive(Debug, Clone, PartialEq)]
pub struct Class {
    pub local: RcLocal,
    pub name: String,
    pub properties: Vec<String>,
    pub methods: Vec<ClassMethod>,
}

has_side_effects!(Class);

impl Class {
    pub fn new(local: RcLocal, name: String) -> Self {
        Self {
            local,
            name,
            properties: Vec::new(),
            methods: Vec::new(),
        }
    }
}

impl Traverse for Class {
    fn rvalues(&self) -> Vec<&RValue> {
        self.methods.iter().map(|m| &m.value).collect()
    }

    fn rvalues_mut(&mut self) -> Vec<&mut RValue> {
        self.methods.iter_mut().map(|m| &mut m.value).collect()
    }
}

impl LocalRw for Class {
    fn values_read(&self) -> Vec<&RcLocal> {
        self.methods.iter().flat_map(|m| m.value.values_read()).collect()
    }

    fn values_read_mut(&mut self) -> Vec<&mut RcLocal> {
        self.methods
            .iter_mut()
            .flat_map(|m| m.value.values_read_mut())
            .collect()
    }

    fn values_written(&self) -> Vec<&RcLocal> {
        vec![&self.local]
    }

    fn values_written_mut(&mut self) -> Vec<&mut RcLocal> {
        vec![&mut self.local]
    }
}

impl fmt::Display for Class {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Formatter {
            indentation_level: 0,
            indentation_mode: Default::default(),
            output: f,
        }
        .format_class(self)
    }
}
