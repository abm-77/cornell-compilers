use serde_json::json;
use serde_json::Value;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::io::{self, BufRead};
use std::ops::Add;
use std::ops::AddAssign;
use std::str::FromStr;

type JSONResult<T> = Result<T, serde_json::Error>;
type Graph<'a> = HashMap<&'a String, HashSet<&'a String>>;

#[derive(Debug, Clone)]
struct BasicBlock {
    instructions: Vec<Value>,
}
impl BasicBlock {
    fn last(&self) -> Option<&Value> {
        self.instructions.last()
    }
    fn new(instructions: Vec<Value>) -> Self {
        Self { instructions }
    }
    fn len(&self) -> usize {
        self.instructions.len()
    }
    fn iter(&self) -> std::slice::Iter<'_, Value> {
        self.instructions.iter()
    }
}

struct Function {
    pub name: String,
    pub basic_blocks: Vec<(String, BasicBlock)>,
}

impl Function {
    fn new(name: String, basic_blocks: Vec<(String, BasicBlock)>) -> Self {
        Self { name, basic_blocks }
    }
}

struct Program {
    functions: Vec<Function>,
}

impl Program {
    fn new(functions: Vec<Function>) -> Self {
        Self { functions }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum LVNValue {
    IntConst(i64),
    BoolConst(bool),
    Value(i64),
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct LVNTableEntry {
    op: String,
    args: Vec<LVNValue>,
}

// CFG has program's lifetime
#[derive(Debug)]
struct CFG<'a> {
    entry: String,
    blocks: HashMap<&'a String, &'a mut BasicBlock>,
    predecessors: Graph<'a>,
    successors: Graph<'a>,
    dominators: Graph<'a>,
}

impl<'a> CFG<'a> {
    fn new(
        entry: String,
        blocks: HashMap<&'a String, &'a mut BasicBlock>,
        predecessors: Graph<'a>,
        successors: Graph<'a>,
        dominators: Graph<'a>,
    ) -> Self {
        Self {
            entry,
            blocks,
            predecessors,
            successors,
            dominators,
        }
    }

    fn pred2succ_distance(&self, pred: &String, succ: &String) -> i32 {
        let mut dist = -1;
        let mut worklist = vec![(pred, 0)];
        while !worklist.is_empty() {
            let (curr, d) = worklist.pop().unwrap();
            if curr == succ {
                dist = d;
                break;
            }

            if let Some(succs) = self.successors.get(curr) {
                for s in succs {
                    worklist.push((s, d + 1));
                }
            }
        }
        dist
    }

    fn dominanator_tree(&self) -> Graph<'a> {
        let mut dom_tree = Graph::new();
        for (bb, domintators) in self.dominators.iter() {
            if self.dominators.len() < 2 {
                continue;
            }

            let mut min = (bb, std::i32::MAX);
            for dom in domintators {
                if dom == bb {
                    continue;
                }

                let dist = self.pred2succ_distance(dom, bb);
                if dist < min.1 {
                    min = (dom, dist);
                }
            }
            dom_tree.entry(min.0).or_default().insert(bb);
        }
        dom_tree
    }

    fn get_imm_dom(&self, bb: &'a String) -> &'a String {
        let mut curr_imm_dom = bb;
        for (dom, subs) in self.dominanator_tree() {
            if subs.contains(bb) {
                curr_imm_dom = dom;
                break;
            }
        }
        curr_imm_dom
    }

    fn dominance_frontiers(&self) -> Graph<'a> {
        let mut dom_front = Graph::new();
        for block in self.blocks.keys() {
            if let Some(preds) = self.predecessors.get(block) {
                if preds.len() < 2 {
                    continue;
                }
                for pred in preds {
                    let mut run_dom;
                    let mut runner = pred;
                    while *runner != self.get_imm_dom(block) {
                        dom_front.entry(&runner).or_default().insert(block);
                        run_dom = self.get_imm_dom(runner);
                        runner = &run_dom;
                    }
                }
            }
        }
        dom_front
    }
}

fn group_block_instrs(func: Value) -> Vec<Vec<Value>> {
    let mut blocks = Vec::new();
    let mut curr_block = Vec::new();
    let instrs = func["instrs"].as_array().unwrap();
    for instr in instrs {
        if let Some(op) = instr["op"].as_str() {
            curr_block.push(instr.clone());
            if op == "jmp" || op == "br" || op == "ret" {
                // op is terminator
                blocks.push(curr_block.clone());
                curr_block.clear();
            }
        } else {
            if curr_block.len() > 0 {
                blocks.push(curr_block.clone());
            }
            curr_block = vec![instr.clone()];
        }
    }
    if curr_block.len() > 0 {
        blocks.push(curr_block.clone());
    }
    blocks
}

fn make_blocks(func: Value) -> Vec<(String, BasicBlock)> {
    let grouped_instrs = group_block_instrs(func);
    let mut blocks = Vec::new();
    for (i, group) in grouped_instrs.into_iter().enumerate() {
        println!("{:#?}", group);
        let name = if let Some(label) = group[0]["label"].as_str() {
            label.to_string()
        } else {
            format!("b{}", i)
        };
        blocks.push((name, BasicBlock::new(group)));
    }
    blocks
}

fn make_program(program: Value) -> Program {
    let mut functions = Vec::new();
    let funcs = program["functions"].as_array().unwrap();
    for func in funcs.into_iter() {
        let bbs = make_blocks(func.clone());
        let name = String::from(func["name"].as_str().unwrap());
        functions.push(Function::new(name, bbs));
    }
    Program::new(functions)
}

fn make_cfg<'a>(program: &'a mut Program) -> CFG<'a> {
    // label
    let entry = program
        .functions
        .get_mut(0)
        .unwrap()
        .basic_blocks
        .get_mut(0)
        .unwrap()
        .0
        .clone();

    let mut flat_order = vec![vec![]];
    let mut blocks = HashMap::<&String, &mut BasicBlock>::new();
    for func in program.functions.iter_mut() {
        let mut level = vec![];
        for (name, block) in func.basic_blocks.iter_mut() {
            blocks.insert(name, block);
            level.push(name.clone());
        }
        flat_order.push(level);
    }

    // construct cfg
    let mut predecessors = Graph::new();
    let mut successors = Graph::new();
    for func in flat_order {
        for (i, name) in func.iter().enumerate() {
            let name = blocks.keys().find(|s| **s == name).unwrap();
            successors.insert(name, HashSet::new());

            let last = blocks.get(*name).unwrap().last().unwrap();
            if let Some(op) = last["op"].as_str() {
                match op {
                    "jmp" | "br" => {
                        let dest_labels = last["labels"]
                            .as_array()
                            .unwrap_or(&Vec::new())
                            .iter()
                            .map(|x| x.as_str().unwrap().to_string())
                            .collect::<Vec<String>>();

                        for dest in dest_labels.iter() {
                            // need to reference prevously stored string
                            let label = blocks.keys().find(|s| **s == dest).unwrap();
                            successors.get_mut(*name).unwrap().insert(label);
                            predecessors.entry(label).or_default().insert(name);
                        }
                    }
                    "ret" => _ = successors.insert(name, HashSet::new()),
                    _ => {
                        if i + 1 < func.len() {
                            let label = blocks.keys().find(|s| ***s == func[i + 1]).unwrap();
                            successors.get_mut(*name).unwrap().insert(label);
                        }
                    }
                }
            }
        }
    }

    // calculate dominators
    let mut dominators = HashMap::<&String, HashSet<&String>>::new();
    loop {
        let prev_dom = dominators.clone();
        for name in blocks.keys() {
            let mut new_val = HashSet::<&String>::new();
            if let Some(preds) = predecessors.get(name) {
                let mut sets = vec![];
                for p in preds {
                    if let Some(p_doms) = dominators.get(p) {
                        sets.push(p_doms);
                    }
                }
                if sets.len() > 0 {
                    let (intersection, others) = sets.split_at_mut(1);
                    let mut intersection = intersection[0].clone();
                    others
                        .iter()
                        .for_each(|other| intersection.retain(|e| other.contains(e)));
                    new_val.extend(intersection);
                }
            }
            new_val.insert(name);
            dominators.insert(name, new_val);
        }
        if dominators == prev_dom {
            break;
        }
    }

    CFG::new(entry, blocks, predecessors, successors, dominators)
}

fn reach(cfg: &CFG) {
    let mut bfs = vec![&cfg.entry];
    let mut vcs = HashMap::<String, i32>::new();
    let mut gen = HashMap::<&String, HashSet<String>>::new();
    let mut kill = HashMap::<&String, HashSet<String>>::new();
    let mut visited = HashSet::<&String>::new();

    // make the gen and kill sets
    while !bfs.is_empty() {
        let name = bfs.pop().unwrap();
        if visited.contains(name) {
            continue;
        }
        visited.insert(name);

        let b = cfg.blocks.get(name).unwrap();
        for instr in b.instructions.iter() {
            if let Some(dest) = instr["dest"].as_str() {
                *vcs.entry(dest.to_string()).or_default() += 1;
                let version = *vcs.get(dest).unwrap();

                gen.entry(name)
                    .or_default()
                    .insert(format!("{dest}{version}"));

                for i in 0..=version {
                    kill.entry(name).or_default().insert(format!("{dest}{i}"));
                }
            }
        }

        for s in cfg.successors.get(name).unwrap() {
            bfs.push(s);
        }
    }

    println!("gen: {:#?}", gen);
    println!("kill: {:#?}", kill);

    let mut ins = HashMap::<&String, HashSet<&String>>::new();
    let mut outs = HashMap::<&String, HashSet<&String>>::new();
    let mut worklist = vec![&cfg.entry];
    while !worklist.is_empty() {
        let bb = worklist.pop().unwrap();

        // merge
        if let Some(preds) = cfg.predecessors.get(bb) {
            preds.iter().for_each(|p| {
                let out_p = outs.entry(*p).or_default();
                ins.entry(bb).or_default().extend(out_p.iter());
            });
        }

        // transfer: out[b] = (in_b - KILLS) + DEF_b
        let mut transfer = HashSet::new();
        if let Some(input) = ins.get(bb) {
            transfer = input.clone();
        }
        if let Some(k) = kill.get(bb) {
            for killed in k {
                transfer.remove(killed);
            }
        }
        if let Some(g) = gen.get(bb) {
            for genned in g {
                transfer.insert(genned);
            }
        }

        // if out[b] has changed
        let out_start = outs.entry(bb).or_default().clone();
        outs.insert(bb, transfer);
        if *outs.get(bb).unwrap() != out_start {
            let success = cfg.successors.get(bb).unwrap();
            for s in success {
                worklist.push(s);
            }
        }
    }

    print!("in: {:#?}", ins);
    print!("out: {:#?}", outs);
}

fn dce(function: &mut Function) {
    loop {
        let mut used = HashSet::new();
        let mut eliminated = 0;
        for (_, bb) in function.basic_blocks.iter_mut() {
            loop {
                let mut assigned = HashSet::new();
                let mut keep = Vec::with_capacity(bb.len());
                let mut redundant = 0;
                for instr in bb.iter() {
                    if let Some(dest) = instr["dest"].as_str() {
                        let dest = String::from(dest);
                        let elim = assigned.contains(&dest) && !used.contains(&dest);
                        keep.push(!elim);
                        if elim {
                            println!("removing redundant assign to {}", dest);
                            redundant += 1;
                        }
                        assigned.insert(dest);
                    } else {
                        keep.push(true);
                    }

                    if let Some(args) = instr["args"].as_array() {
                        for arg in args {
                            let var_name = String::from(arg.as_str().unwrap());
                            used.insert(var_name);
                        }
                    }
                }
                let mut it = keep.into_iter();
                bb.instructions.retain(|_| it.next().unwrap());
                if redundant == 0 {
                    break;
                }
            }
        }
        for (_, bb) in function.basic_blocks.iter_mut() {
            bb.instructions.retain(|instr| {
                if let Some(dest) = instr["dest"].as_str() {
                    if !used.contains(dest) {
                        println!("eliminating variable: {}", dest);
                        eliminated += 1;
                        return false;
                    }
                }
                return true;
            });
        }
        if eliminated == 0 {
            break;
        }
    }
}

fn lvn(bb: &mut BasicBlock) {
    let mut next_num: i64 = 0;
    let mut table = HashMap::<LVNTableEntry, (i64, String)>::new();
    let mut num2val = HashMap::<i64, LVNTableEntry>::new();
    let mut var2num = HashMap::<String, i64>::new();

    for instr in bb.instructions.iter_mut() {
        if instr["label"].as_str().is_some() {
            continue;
        }

        let op = String::from(instr["op"].as_str().unwrap());
        let mut arg_values = Vec::new();
        if let Some(args) = instr["args"].as_array() {
            for arg in args {
                let v = var2num.get(arg.as_str().unwrap()).unwrap();
                arg_values.push(LVNValue::Value(*v));
            }
        } else if let Some(ival) = instr["value"].as_i64() {
            arg_values = vec![LVNValue::IntConst(ival)];
        } else if let Some(bval) = instr["value"].as_bool() {
            arg_values = vec![LVNValue::BoolConst(bval)];
        }
        let value = LVNTableEntry {
            op,
            args: arg_values,
        };

        if table.contains_key(&value) {
            let (_, var) = table.get(&value).unwrap();
            *instr = json!({ "args": [var], "op": "id"});
        } else {
            if instr["dest"].as_str().is_none() {
                continue;
            }

            let num = next_num;
            next_num += 1;

            let dest = String::from(instr["dest"].as_str().unwrap());
            // TODO: do smth here where we detect if an instruction will later
            // be overwritten

            table.insert(value.clone(), (num, dest.clone()));

            if let Some(args) = instr["args"].as_array_mut() {
                for arg in args.iter_mut() {
                    let name = table
                        .get(
                            num2val
                                .get(var2num.get(arg.as_str().unwrap()).unwrap())
                                .unwrap(),
                        )
                        .unwrap()
                        .1
                        .clone();
                    *arg = Value::from(name);
                }
            }
            var2num.insert(dest.clone(), num);
            num2val.insert(num, value.clone());
        }
    }

    println!("{:?}", table);
    println!();
    println!("{:?}", num2val);
    println!();
    println!("{:?}", var2num);
    println!();
    println!("{:?}", bb);
}

fn to_ssa(cfg: &mut CFG) {
    // find definitions
    let mut defs = HashMap::<String, HashSet<&String>>::new();
    for (name, bb) in cfg.blocks.iter() {
        for instr in bb.instructions.iter() {
            if let Some(dest) = instr["dest"].as_str() {
                defs.entry(dest.to_string()).or_default().insert(name);
            }
        }
    }

    // place phi nodes at junctions
    let dom_fronts = cfg.dominance_frontiers();
    let mut phi_placements = HashMap::<&String, HashSet<String>>::new();
    loop {
        let old_defs = defs.clone();
        for (var, defsites) in old_defs.iter() {
            for defsite in defsites.iter() {
                if let Some(df) = dom_fronts.get(defsite) {
                    for node in df {
                        phi_placements.entry(node).or_default().insert(var.clone());
                        if !defsites.contains(*node) {
                            defs.entry(var.clone()).or_default().insert(node);
                        }
                    }
                }
            }
        }

        if old_defs == defs {
            break;
        }
    }

    // rename variables
    let dtree = cfg.dominanator_tree();
    let mut worklist = vec![&cfg.entry];
    let mut stack = HashMap::<&String, Vec<String>>::new();
    let mut vcs = HashMap::<&String, i32>::new();
    let mut phi_dests = HashMap::<(&String, &String), String>::new();
    let mut phi_args = HashMap::<(&String, &String), Vec<String>>::new();

    for v in defs.keys() {
        vcs.insert(v, 0);
        stack.insert(v, vec![format!("{}.0", v)]);
    }

    while !worklist.is_empty() {
        let bb_name = worklist.pop().unwrap();
        let bb = cfg.blocks.get_mut(bb_name).unwrap();
        let old_stack = stack.clone();

        if let Some(phi_vars) = phi_placements.get(bb_name) {
            for var in phi_vars {
                let version = *vcs.get(var).unwrap();
                let new = format!("{}.{}", var, version);
                vcs.get_mut(var).unwrap().add_assign(1);
                stack.get_mut(var).unwrap().push(new);
                phi_dests.insert(
                    (bb_name, var),
                    stack.get(var).unwrap().last().unwrap().clone(),
                );
            }
        }

        for instr in bb.instructions.iter_mut() {
            if let Some(args) = instr["args"].as_array_mut() {
                for arg in args.iter_mut() {
                    let old = arg.as_str().unwrap().to_string();
                    println!("{old}");
                    let top = stack.get(&old).unwrap().last().unwrap();
                    *arg = json!(top);
                }
            }

            if let Some(dest) = instr["dest"].as_str() {
                let old = dest.to_string();
                let version = *vcs.get(&old).unwrap();
                let new = format!("{}.{}", old, version);
                vcs.get_mut(&old).unwrap().add_assign(1);
                stack.get_mut(&old).unwrap().push(new);
                instr["dest"] = json!(stack.get(&old).unwrap().last().unwrap());
            }
        }

        if let Some(succs) = cfg.successors.get(bb_name) {
            for succ in succs {
                if let Some(phi_vars) = phi_placements.get(succ) {
                    for var in phi_vars {
                        if stack.contains_key(var) {
                            phi_args.entry((succ, var)).or_default().extend(vec![
                                bb_name.clone(),
                                stack.get(var).unwrap().last().unwrap().clone(),
                            ]);
                        } else {
                            phi_args
                                .entry((succ, var))
                                .or_default()
                                .extend(vec![bb_name.clone(), String::from("__undefined")]);
                        }
                    }
                }
            }
        }

        if let Some(subs) = dtree.get(bb_name) {
            worklist.extend(subs.iter().filter(|s| **s != bb_name));
        }

        stack.clear();
        stack.extend(old_stack);
    }

    // insert phi instructions
    for ((dest, old), new) in phi_dests {
        let bb = cfg.blocks.get_mut(dest).unwrap();
        let args = phi_args.get(&(dest, old)).unwrap();
        bb.instructions
            .insert(0, json!({"op": "phi", "args": args, "dest": new}));
    }
}

fn from_ssa(cfg: &mut CFG) {
    let mut locations = Vec::new();
    for (_, bb) in cfg.blocks.iter_mut() {
        bb.instructions.retain_mut(|instr| {
            if instr["op"].as_str().is_some_and(|op| op == "op") {
                let args = instr["args"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|v| v.as_str().unwrap().to_string())
                    .collect::<Vec<String>>();
                args.chunks(2).for_each(|pair| {
                    locations.push((
                        pair[0].clone(),
                        instr["dest"].as_str().unwrap().to_string(),
                        pair[1].clone(),
                    ));
                });
                return false;
            }
            return true;
        });
    }

    for (pred, dest, val) in locations {
        let pred_bb = cfg.blocks.get_mut(&pred).unwrap();
        pred_bb.instructions.push(json!({
            "op": "id",
            "dest": dest,
            "args": [val],
        }));
    }
}

// find node with no children and add a print instrction
fn simple_cfg_transform(cfg: &mut (Vec<(String, BasicBlock)>, HashMap<String, Vec<String>>)) {
    for (label, block) in cfg.0.iter_mut() {
        let s = cfg.1.get_mut(label).unwrap();
        if s.is_empty() {
            block
                .instructions
                .push(json!({"args": ["i have no children"], "op": "print"}));
        }
    }
}

fn main() -> JSONResult<()> {
    let stdin = io::stdin();
    let mut data = String::new();
    for line in stdin.lock().lines() {
        data.push_str(line.unwrap().as_str());
    }

    let json: Value = serde_json::from_str(data.as_str())?;
    let mut program = make_program(json);
    let mut cfg = make_cfg(&mut program);
    //let _ = cfg.dominance_frontiers();
    to_ssa(&mut cfg);
    from_ssa(&mut cfg);
    println!("{:#?}", cfg.blocks);

    Ok(())
}
