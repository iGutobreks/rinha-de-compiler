use std::collections::HashMap;

use serde_derive::Deserialize;

#[derive(Debug, Deserialize, Clone)]
pub struct File {
  name: String,
  expression: Term,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Int {
  value: i32,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Str {
  value: String,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Print {
  value: Box<Term>,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Binary {
  rhs: Term,
  op: BinaryOp,
  lhs: Term,
}

#[derive(Debug, Deserialize, Clone)]
pub enum BinaryOp {
  Add,
  Sub,
  Mul,
  Lt,
  Gt,
}

#[derive(Debug, Deserialize, Clone)]
pub struct If {
  then: Term,
  condition: Term,
  otherwise: Term,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Bool {
  value: bool,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Tuple {
  first: Term,
  second: Term,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Let {
  name: Parameter,
  value: Term,
  next: Term,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Parameter {
  text: String
}

#[derive(Debug, Deserialize, Clone)]
pub struct Var {
  text: String
}

#[derive(Debug, Deserialize, Clone)]
pub struct Function {
  parameters: Vec<Parameter>,
  value: Term,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Call {
  callee: Term,
  arguments: Vec<Term>,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(tag = "kind")]
pub enum Term {
  Int(Int),
  Str(Str),
  Print(Print),
  Binary(Box<Binary>),
  If(Box<If>),
  Bool(Bool),
  Tuple(Box<Tuple>),
  Let(Box<Let>),
  Function(Box<Function>),
  Var(Var),
  Call(Box<Call>),
}

type Func_name = String;
type Env = std::collections::HashMap<Func_name, Option<Vec<(String, Term)>>>;
type Env_Arguments = std::collections::HashMap<Func_name, Option<Vec<(String, Term)>>>;

#[derive(Debug, Deserialize, Clone)]
pub struct Storage {
  parameters: Vec<Parameter>,
  table: Option<Env>,
}

#[derive(Debug, Deserialize, Clone)]
pub enum Val {
  Void,
  Int(i32),
  Bool(bool),
  Str(String),
  Tuple((i32, i32)),
  Callee(Env),
  Var(String, Option<Storage>),
}

mod helper {
    use crate::{Val, Term, Parameter, Int, Binary, BinaryOp, eval};

    pub fn associety_arguments(val: Val) -> Vec<(String, Term)> {
     let func_name: String = match val.clone() {
        Val::Var(str, _) => str,
        _ => panic!("cannot find name of function"),
     }; 

     let storage = match val {
         Val::Var(_, env) => match env {
             Some(s) => s,
             None => {eprintln!("this is none"); return vec![]},
         },
         _ => panic!("cannot find the kind"),
     }; //get storage parameters/arguments

     let parameters = storage.parameters;
     let table = storage.table.expect("table is none");

     let table = table.get(&func_name).expect("table is none").as_ref().expect("inside table no have values");

     let mut new_table: Vec<(String, Term)> = Vec::new();

     if &table.len() != &parameters.len() {
         panic!("diff bettewen arguments and parameters");
     }

     for tl in 0..table.into_iter().len() {
         new_table.push(((parameters[tl].text).clone(), (table[tl].1).clone()));
     }

     new_table
    }

    pub fn change_env(env: Vec<(String, Term)>, var_name: String, number_rhs: Term, operation: BinaryOp) -> Term {
        let mut number: Term = Term::Int(Int { value: 0 });        

        for i in 0..env.len() {
            if env[i].0 == var_name {
                match &env[i].1 {
                    Term::Int(int) => {number = Term::Int(int.clone()); break;},
                    _ => panic!("not is a number"),
                };
            }
        }

        let binary = Binary { lhs: number, op: operation, rhs: number_rhs };
        let arithmetic = eval(Term::Binary(Box::new(binary)), None); //make arithmetic bettewen the
                                                                     //numbers

        let arithmetic = match arithmetic {
            Val::Int(int) => Term::Int(Int { value: int }),
            _ => panic!("not is a number"),
        };

        arithmetic
    }
}

fn eval(term: Term, mut env: Option<&mut Storage>) -> Val {
  dbg!(&env);

  let mut func_name = String::new();
  let mut storage = Storage { parameters: vec![], table: None };

  if let Some(_env) = env {
      storage = Storage { 
          parameters: _env.clone().parameters,
          table: _env.clone().table,
      };
  }

  match term {
    Term::Int(number) => Val::Int(number.value),
    Term::Str(str) => Val::Str(str.value),
    Term::Print(print) => {
      let val = eval(*print.value, Some(&mut storage));
      match val {
        Val::Int(number) => println!("{number}"),
        Val::Bool(boolen) => println!("{boolen}"),
        Val::Str(string) => println!("{string}"),
        _ => panic!("value not supported"),
      };
      Val::Void
    }
    Term::Binary(bin) => {
      let lhs = eval(bin.lhs, Some(&mut storage));
      let rhs = eval(bin.rhs, Some(&mut storage));

      if let (Val::Int(a), Val::Int(b)) = (lhs.clone(), rhs.clone()) {
        return Val::Int(match bin.op {
          BinaryOp::Add => {
            a+b
          },
          BinaryOp::Sub => {
            a-b
          },
          BinaryOp::Mul => {
            a*b
          },
          BinaryOp::Gt => {
            if dbg!(a > b) {
              return Val::Bool(true);
            }
            return Val::Bool(false);
          },
          BinaryOp::Lt => {
            if dbg!(a < b) {
              return Val::Bool(true);
            }
            return Val::Bool(false);
          }
        })
      } else if let (Val::Str(a), Val::Int(b)) = (lhs.clone(), rhs.clone()) {
        return Val::Str(match bin.op {
          BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => {
            format!("{}{}", a, b)
          },
          BinaryOp::Gt | BinaryOp::Lt => {
            todo!()
          },
        })
      } else if let (Val::Int(a), Val::Str(b)) = (lhs.clone(), rhs.clone()) {
        return Val::Str(match bin.op {
          BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => {
            format!("{}{}", b, a)
          },
          BinaryOp::Gt | BinaryOp::Lt => {
              todo!()
          },
        })
      } else {
        match (lhs, rhs) {
          (Val::Void, Val::Int(a)) | (Val::Int(a), Val::Void) => return dbg!(Val::Int(a)),
          (Val::Void, Val::Str(a)) | (Val::Str(a), Val::Void) => return dbg!(Val::Str(a)),
          (Val::Var(a, _env), Val::Int(b)) | (Val::Var(a, _env), Val::Int(b)) => {
              dbg!(_env);

              Val::Void
          },
          (Val::Str(a), Val::Var(b, c)) => {
              let arguments = helper::associety_arguments(Val::Var(b, c)); //values of parameters,
                                                                           //refered by arguments 

              Val::Str(format!("{}{:?}", a, arguments))
          }
          e => panic!("not is a number or string, {e:?}"),
        }
      }
    },
    Term::If(i) => {
      println!("{i:?}");
      let condition = eval(i.condition, Some(&mut storage));
      match condition {
        Val::Bool(true) => eval(i.then, Some(&mut storage)),
        Val::Bool(false) => eval(i.otherwise, Some(&mut storage)),
        con => panic!("error in condition: {con:?}"),
      }
    },
    Term::Bool(boolean) => Val::Bool(boolean.value),
    Term::Tuple(tp) => {
      let tp_first = eval(tp.first, Some(&mut storage));
      let tp_second = eval(tp.second, Some(&mut storage));

      Val::Tuple(match (tp_first, tp_second) {
        (Val::Int(a), Val::Int(b)) => (a, b),
        _ => panic!("not is a number"),
      })
    },
    Term::Let(var) => {
      func_name = var.name.text;
      let parameters = match (var.value).clone() {
          Term::Function(func) => func.parameters,
          _ => panic!("dont have parameters in value"),
      }; // get parameters of value
         
      storage.parameters = parameters;
         
      let callee = eval(var.next, Some(&mut storage)); //callee and arguments
      let value = eval(dbg!(var.value), Some(&mut storage)); //body of function with your parameters
    
      Val::Void
    },
    Term::Function(func) => {
      dbg!(&func);
      let parameters = &func.parameters;
      let value = eval(func.value, Some(&mut storage));

      Val::Void
    },
    Term::Var(var) => {  
      Val::Var(var.text, Some(storage))
    },
    Term::Call(cl) => {
      let callee = match eval(cl.callee, Some(&mut storage)) {
          Val::Var(tx, _) => tx,
          _ => panic!("not is a var"),
      }; // get the value of callee, is this a name of callee function

      let mut arguments_order: Vec<(String, Term)> = Vec::new();

      for argument in cl.arguments {
        arguments_order.push(("null".to_string(), argument));
      }

      let arguments_order = Some(arguments_order);
      if let Some(mut existing_storage) = storage.table {
        existing_storage.insert(callee.clone(), arguments_order.clone());
        storage.table = Some(existing_storage);
      } else {
        let mut table = std::collections::HashMap::from([(callee.clone(), arguments_order.clone())]);
        storage.table = Some(table);
      }

      println!("{arguments_order:?}\n{storage:?}\n{callee:?}");
      Val::Var(callee, Some(storage))
    },
  }
}

fn main() {
  let program = std::fs::read_to_string("../interpreter/read.json").unwrap();
  let program: File = serde_json::from_str(&program).unwrap();

  let term = program.expression;
  println!("{:?}", eval(term, None));
}
