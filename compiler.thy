theory compiler imports Main
begin


(*
  Compiles expressions consisting of variables,constants and binary ops to a stack machine.
  Execution of the stack machine is modelled by 'exec', which takes in a list of instructions, a environment (ie address -> value mapping) and a stack, and returns the stack at the end of execution.

  exec :: ('a,'v) instr list => ('a => 'v) => 'v list models execution of the stack machine. It takes as INPUT a list of instructions, an environment (ie address -> value mapping) and a stack, and it OUTPUTs the stack at the end of execution.

  The lemmas prove the correctness of the compiler; ie that the execution of a compiled expression results in the value of the expression

*)

type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"
datatype ('a,'v) exp = Cex 'v | Vex 'a | Bex "'v binop" "('a,'v)exp" "('a,'v)exp"

datatype ('a,'v) instr = Const 'v | Load 'a | Apply "'v binop"


primrec valuep :: "('a,'v) exp \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v" where
  "valuep (Cex v) env = v" |
  "valuep (Vex v) env = env v" |
  "valuep (Bex op e1 e2) env = op (valuep e1 env) (valuep e2 env)"


primrec exec :: "('a,'v) instr list \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v list \<Rightarrow> 'v list" 
  where
  "exec [] env stack = stack" |
  "exec (x#xs) env stack = (case x of
     Const v \<Rightarrow> exec xs env (v#stack)
   | Load a \<Rightarrow> exec xs env ((env a) # stack)
   | Apply f \<Rightarrow> exec xs env ((f (hd stack) (hd (tl stack))) # (tl (tl stack))))"

primrec compile :: "('a,'v)exp \<Rightarrow> ('a,'v) instr list" 
  where
  "compile (Cex v) = [Const v]" |
  "compile (Vex a) = [Load a]" |
  "compile (Bex f x y) = compile y @ compile x @ [(Apply f)]"


lemma exec_app[simp]: "ALL vs. exec (xs@ys) s vs = exec ys s (exec xs s vs)"
  apply(induction xs)
   apply(simp)
  apply(simp)
    apply(split instr.split)
  apply(simp split: instr.split)
  done


theorem "ALL xs. exec (compile e) s xs = (valuep e s) # xs"
  apply(induction e)
    apply(simp)
  apply(auto)


end











