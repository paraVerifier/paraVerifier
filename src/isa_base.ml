
let para_theory =
"theory paraTheory imports Main Finite_Set
begin

section{*Main defintions*}

text{*
According to the aforementioned discussion in section ?, firstly we define the variables used in the protocols. 
There are two kinds of variables, global and parameterized (local) 
variables. In hardware implemetations of the protocols, 
the variables are implenteed as registers in global or local modules. *}

datatype varType=Ident  string | Para varType  nat |Field  varType   string 

text{*For instance, $\\mathsf{Global}~ \"x\"$ and Para \"n\" 1 are used to formalize the global variable $x$ and the local variable $n[1]$ in the Murphi program listed in section ?*.

An expression used in this work is rather simple, which is a variable or constant. In our model,  a value of a variable is
 just a natural number.  A boolean variable is encodes as 0 or 1. A value is obtained from reading a variable or  being assigned directly by a natural number.  
 *}
 
definition ex0P::\"nat \\<Rightarrow> (bool) \\<Rightarrow>bool\" 
 where [simp]:  \"ex0P N P \\<equiv>P\" 

definition ex1P::\"nat \\<Rightarrow> (nat \\<Rightarrow> bool) \\<Rightarrow>bool\" 
 where [simp]:  \"ex1P N P \\<equiv> \\<exists>i. ( i\\<le> N \\<and> P i )\"


definition ex2P::\"nat \\<Rightarrow> (nat \\<Rightarrow> nat \\<Rightarrow> bool) \\<Rightarrow>bool\"
 where [simp]:  \"ex2P N P \\<equiv> \\<exists>i j. ( i\\<le> N  \\<and>j\\<le> N \\<and> i\\<noteq>j \\<and> P i j )\"

definition ex3P::\"nat \\<Rightarrow> (nat \\<Rightarrow> nat \\<Rightarrow>nat\\<Rightarrow> bool) \\<Rightarrow>bool\"
 where [simp]: \"ex3P N P \\<equiv> \\<exists>i j k. ( i\\<le> N  \\<and>j\\<le> N \\<and> k \\<le>N \\<and>  i\\<noteq>j \\<and>  i\\<noteq>k \\<and>  j\\<noteq>k \\<and> P i j k)\"
 
 
primrec down ::\"nat \\<Rightarrow>nat list\" where
\"down 0=[0]\" |
\"down (Suc n)=Suc n #(down n)\"

datatype scalrValueType=enum string string |index nat | boolV bool

datatype expType= IVar varType   |  
         Const scalrValueType |
         iteForm formula  expType  expType 

and 
 formula = eqn expType expType|
                andForm  formula formula |
                 neg formula|
                orForm formula formula | 
                implyForm formula formula |
                chaos 

type_synonym assignType=  \"varType \\<times>   expType\"

text{*A statement is is just a lists of assignments, but these assignments are extecuted in parallel, \\emph{not} in a sequential order*}
datatype statement=  assign assignType          |
                  parallel assignType  statement


text{*A parameterized statement is just a function from a parameter to a statement. For conveniece, we also define the concatation of statements, and use it to define the $\\mathsf{forall}$ statement.*}
type_synonym paraStatement= \"nat \\<Rightarrow> statement\"


primrec cat::\"statement \\<Rightarrow> statement \\<Rightarrow>statement\" where
cat1:\"cat (assign a) S=parallel a S\" |
cat2:\"cat (parallel a S1) S=parallel a (cat S1 S)\"

fun parallelList::\"statement list \\<Rightarrow> statement\" where
\"parallelList [S] = S\"|
\"parallelList (S1#SL) = cat S1 (parallelList (SL))\" 

fun  forallSent::\"nat list\\<Rightarrow>paraStatement \\<Rightarrow> statement\"  where
oneSent: \"forallSent ([i])  paraS = paraS i\"|
moreSent:\" forallSent  (i#xs ) paraS=cat (paraS i) (forallSent (xs) paraS)  \" 
 

text{* The simplest formula is equivalence between expressions. Negation, conjunction, disjunction, and implicattion formulas are also defined. A parameterized formula is just a function from a natural number to a formula.*}

text{*Similarly, a parameterized formula is a function from a parameter to a formula. We also define
 the $\\mathsf{forall}$ and $mathsf{exists}$ formulas$.*}
type_synonym paraFormula=\"nat \\<Rightarrow> formula\"

fun forallForm::\"nat list \\<Rightarrow>paraFormula \\<Rightarrow> formula\" where
oneAllForm: \"forallForm [i] forms = forms i\"|
moreAllForm: \"forallForm (i#j#xs)  forms = andForm (forms i) (forallForm (j#xs)  forms)\"


fun existsForm::\"nat list \\<Rightarrow>paraFormula \\<Rightarrow> formula\" where
oneExForm: \" existsForm [i] forms = forms i\"|
moreExForm: \" existsForm (i#j#xs)  forms = orForm (forms i) (forallForm (j#xs)  forms)\"






text{*With the formalizatiion of formula and statement, it is natural to define a rule. A guard and
 statement of a rule are also defined for convenience. *}
datatype rule =  guard formula  statement



primrec pre::\"rule \\<Rightarrow> formula\" where
\"pre (guard f a)=f\"

primrec act::\"rule \\<Rightarrow>statement\" where
\"act  (guard f a)=a\"


text{*A parameterized rule is just from a natural number to a rule.*}
type_synonym paraRule=\" nat \\<Rightarrow> rule\"




section{*semantics of a protocol*}
text{*A  state of a protocol  is an instantaneous snapshot of its  behaviour given by an assignment of  values to variables of
the circuit. Therefore, we define:*}

type_synonym state= \"varType \\<Rightarrow> scalrValueType \"

text{*The formal semantics of an expression and a formula is formalized as follows:*}
primrec expEval :: \"expType \\<Rightarrow> state \\<Rightarrow> scalrValueType\" and 
 formEval :: \"formula \\<Rightarrow> state \\<Rightarrow>bool\"  where
 
\"expEval  (IVar ie) s =  ( s ie)\" |
\"expEval  (Const i) s =  i\"  |
\"expEval  (iteForm f e1 e2) s= 
   ( if (formEval f s) then     (expEval e1 s)
   else (expEval e2 s))\"  |

evalExp: \"formEval (eqn e1 e2) s= ((expEval e1 s) = (expEval e2 s))\" |
evalAnd: \"formEval ( andForm f1 f2) s=( (formEval f1 s) \\<and> (formEval f2 s))\"|
evalNeg: \"formEval (neg f1 ) s= ( \\<not>(formEval f1 s))\"|
evalOr: \"formEval (orForm f1 f2) s=( (formEval f1 s) \\<or>  (formEval f2 s))\"|
evalImp:\"formEval (implyForm f1 f2) s= ( (formEval f1 s) \\<longrightarrow>  (formEval f2 s))\" |
\"formEval chaos s=True\"


text{*A state transition from a state to another sate, which is caused by an execution of a statement, is
 defined as follows:*}

primrec statement2Assigns::\"statement \\<Rightarrow> assignType list\" where
\"statement2Assigns (assign asgn)=[asgn]\" |
\"statement2Assigns (parallel a S)=a#statement2Assigns S\"

definition wellformedAssgnList::\"assignType list => bool\" where
\" wellformedAssgnList asgns\\<equiv>distinct (map fst asgns)\"

primrec transAux:: \"assignType list \\<Rightarrow> state \\<Rightarrow>state \" where
\"transAux [] s= s \" |
\"transAux (pair#asgns) s=( transAux asgns s) ((fst pair):= expEval  (snd pair) s) \"

definition trans:: \"statement \\<Rightarrow> state \\<Rightarrow>state \" where [simp]:
\"trans S s \\<equiv> transAux (statement2Assigns S) s\"

text{*Here we must point out the fact that the assignments in a parallel assignment is executed in parallel, therefore we always assign an evaluation of an expression in the state $s$ to the corresponding variable.*}



text{*The reachable sate set of a protocol, which is describled by a set of initiate formulas and a set of rules, can be formalized inductively as follows:*}


inductive_set reachableSet::\" formula set\\<Rightarrow> rule set \\<Rightarrow>state set\" 
  for  inis::\"formula set\"  and rules::\"rule set\"   where

initState:  \"\\<lbrakk>formEval  ini s; ini \\<in>  inis\\<rbrakk>  \\<Longrightarrow>(  s \\<in>  ( reachableSet inis rules))\" |

oneStep:    \" \\<lbrakk>s \\<in>  reachableSet inis rules ;
               r \\<in>   rules ;formEval (pre r ) s \\<rbrakk> \\<Longrightarrow>  trans  (act r ) s  \\<in>  reachableSet inis rules\"

text{*The rule $\\mathsf{initState}$ says that a state $s$ is in $\\mathsf{reachableSet}~inis~ rules$ if
 there exists a formula $ini$ that is true in state $s$. Next rule $\\mathsf{oneStep}$ says that 
$$\\mathsf{ trans}~  ($\\mathsf{act}~ r )~ s $ is also in
 $\\mathsf{reachableSet}~inis~ rules$ if $s$ already is in 
 $\\mathsf{reachableSet}~inis~ rules$ and $r \\<in> rules$.*}


definition formEquiv::\"formula \\<Rightarrow> formula \\<Rightarrow> bool\" where
\"formEquiv f1 f2\\<equiv> \\<forall> s. formEval f1 s = formEval f2 s\"


type_synonym permutationSet= \" (nat \\<Rightarrow> nat) set\"
 

definition sentEquiv::\"statement \\<Rightarrow> statement \\<Rightarrow> bool\" where
\"sentEquiv S1 S2\\<equiv> \\<forall> s . trans S1 s = trans S2 s\"

definition ruleEquiv::\"rule \\<Rightarrow> rule \\<Rightarrow> bool\" where
\"ruleEquiv r1 r2\\<equiv> formEquiv (pre r1) (pre r2) \\<and> sentEquiv (act r1) (act r2)\" 

primrec onParamVar::\"nat \\<Rightarrow> varType \\<Rightarrow> bool\"  where
\" onParamVar i (Ident v) = False\" |
\" onParamVar i (Para v j) = (if (i=j) then True else  (onParamVar i v ))\"  |
\" onParamVar i (Field v str) =   (onParamVar i v )\"  


primrec onParamExp::\"nat \\<Rightarrow> expType \\<Rightarrow> bool\"  where
\"onParamExp i (IVar v) = onParamVar i  v\" |
\"onParamExp i (Const j) =  False \" 


primrec  onParamCond::\"nat\\<Rightarrow> formula \\<Rightarrow> bool\"  where 
\"onParamCond i  (eqn e1 e2) = ( (onParamExp i e1 ) \\<or>  (onParamExp i e2))\" |
\"onParamCond i  ( andForm f1 f2) =(  (onParamCond i  f1 ) \\<or>  (onParamCond  i f2 ))\"|
\"onParamCond i  (neg f1 ) = (  (onParamCond i  f1 ))\"|
\"onParamCond i  (orForm f1 f2) =(  (onParamCond i f1 )  \\<or>   (onParamCond i f2 ))\"|
\"onParamCond  i (implyForm f1 f2) = (  (onParamCond i f1 ) \\<or>  (onParamCond i f2 ))\"

primrec  onParamSent::\"nat\\<Rightarrow> statement \\<Rightarrow> bool\" where
\" onParamSent i (assign a)=( onParamVar i (fst a)) \"|
\" onParamSent i ( parallel a sent2)= ((onParamVar i (fst a)) \\<or>  (onParamSent i sent2))\"

text{*Functions $\\mathsf{varIsOnVar}~x~x'$, $\\mathsf{varIsOnExp}~x~e$,  $\\mathsf{varIsOnForm}~x~f$, and  $\\mathsf{varIsOnSent}~x~S$ 
define whether a pattern variable $x$  occurs in a target variable $x'$, expression $e$, a formula $f$, and a statement $S$. Namely, $x$ 
occurs in the above targets. 
For instance, for the statement   $S=\\mathsf{assign}~  ((\\mathsf{Para}~  ''n''~ i), (\\mathsf{Const} ~1))$, variable  $x=\\mathsf{Global}~''x''$ does not occur in it, hence $ \\neg  $\\mathsf{varIsOnSent}~x~S$.  *}

definition varIsOnVar::\"varType \\<Rightarrow> varType \\<Rightarrow> bool\"  where  [simp]:
\" varIsOnVar pat  target = (pat =target)\" 

primrec varIsOnExp::\"varType \\<Rightarrow> expType \\<Rightarrow> bool\"  where  
\"varIsOnExp x (IVar v) = varIsOnVar x   v\" |
\"varIsOnExp x (Const j) =  False \" 


primrec  varIsOnForm::\"varType\\<Rightarrow> formula \\<Rightarrow> bool\"  where 
\"varIsOnForm x  (eqn e1 e2) = ( (varIsOnExp x  e1 ) \\<or>  (varIsOnExp x e2))\" |
\"varIsOnForm x  ( andForm f1 f2) =(  (varIsOnForm x f1 ) \\<or>  (varIsOnForm x f2 ))\"|
\"varIsOnForm x  (neg f1 ) = (  (varIsOnForm x  f1 ))\"|
\"varIsOnForm x  (orForm f1 f2) =(  (varIsOnForm x  f1 )  \\<or>   (varIsOnForm x f2 ))\"|
\"varIsOnForm  x (implyForm f1 f2) = (  (varIsOnForm x f1 ) \\<or>  (varIsOnForm x f2 ))\"

primrec  varIsOnSent::\"varType \\<Rightarrow> statement \\<Rightarrow> bool\" where
\" varIsOnSent x (assign a)=( varIsOnVar x (fst a)) \"|
\" varIsOnSent x ( parallel a sent2)= (( varIsOnVar x (fst a)) \\<or>  (varIsOnSent x sent2))\"

primrec assignsOf::\"statement \\<Rightarrow> assignType set\" where
\"assignsOf (assign a) ={a}\" |
\"assignsOf (parallel a S)= {a} \\<union> assignsOf S\"

primrec eqnOnRule::\"formula \\<Rightarrow> rule \\<Rightarrow> bool\"  where
\"eqnOnRule (eqn e1 e2) r=( \\<exists>x. (e1=IVar x) \\<and>(x,e2) \\<in> assignsOf (act r))\"

primrec negEqnOnRule::\"formula \\<Rightarrow> rule \\<Rightarrow> bool\"  where
\"negEqnOnRule (neg f) r=( \\<exists>x e1 e2 e2'. f=  (eqn e1 e2) \\<and> (e1=IVar x) \\<and>(x,e2') \\<in> assignsOf (act r)\\<and> e2 \\<noteq>e2')\"

text{*Function $\\mathsf{statementEnableForm}$ says that formula $f$ will be valid after statement $S$ is executed from any state $s$. On the other hand,  $\\mathsf{statementDisableForm}$ says that formula $f$ must be invalid after statement $S$ is executed from any state $s$ For instance,  for the statement $S=\\mathsf{assign}~  ((\\mathsf{Para}~  ''n''~ 0), (\\mathsf{Const} ~1))$, formula $f_1=  eqn (IVar (Para ''n'' 0)) (Const 1)) $, $f_2= eqn (IVar (Para ''n'' 0)) (Const 2))$, we have $\\mathsf{statementEnableForm}~S~f_1$ and $\\mathsf{statementDisableForm}~S~f_2$.*}
(*definition statementEnableForm::\"statement \\<Rightarrow> formula \\<Rightarrow> bool\" where  [simp]:
\" statementEnableForm S f \\<equiv>
  \\<forall>s. ( formEval f (trans S s))\"

definition statementDisableForm::\"statement \\<Rightarrow> formula \\<Rightarrow> bool\" where  [simp]:
\" statementDisableForm S f \\<equiv>
  \\<forall>s.  (\\<not> formEval f (trans S s))\"
 *)


definition varsOfVar::\" varType \\<Rightarrow> varType set\"  where  [simp]:
\" varsOfVar x  = {x}\" 

primrec varOfExp::\"expType \\<Rightarrow> varType set\"  and
  varOfForm::\"formula \\<Rightarrow> varType set\"  where 
\"varOfExp  (IVar v) =   varsOfVar v\" |
\"varOfExp   (Const j) =  {}\" |

\"varOfExp   (iteForm f e1 e2) =(varOfForm f) \\<union>  (varOfExp   e1 )  \\<union>   (varOfExp  e2)\" |

\"varOfForm   (eqn e1 e2) = ( (varOfExp   e1 )  \\<union>   (varOfExp  e2))\" |
\"varOfForm   ( andForm f1 f2) =(  (varOfForm  f1 )  \\<union>  (varOfForm  f2 ))\"|
\"varOfForm   (neg f1 ) = (  (varOfForm   f1 ))\"|
\"varOfForm   (orForm f1 f2) =(  (varOfForm   f1 )   \\<union>   (varOfForm  f2 ))\"|
\"varOfForm   (implyForm f1 f2) = (  (varOfForm  f1 )  \\<union>  (varOfForm f2 ))\"|
\"varOfForm   (chaos) ={}\"

primrec  varOfSent::\"statement \\<Rightarrow> varType set\" where
\" varOfSent  (assign a)=( varsOfVar  (fst a)) \"|
\" varOfSent  ( parallel a sent2)= (( varsOfVar  (fst a)) \\<union>  (varOfSent  sent2))\"

(*primrec  varOfSentL::\"statement \\<Rightarrow> varType set\" where
\" varOfSentL  (assign a)=( varsOfVar  (fst a)) \"|
\" varOfSentL  ( parallel a sent2)= (( varsOfVar  (fst a)) \\<union>  (varOfSent  sent2))\"*)



definition invHoldForRule2::\" formula \\<Rightarrow> rule \\<Rightarrow> bool\" where
\"invHoldForRule2 f  r \\<equiv>   (varOfSent (act r)) \\<inter> (varOfForm f)={} \"




primrec conjs::\"formula \\<Rightarrow> formula set\" where
\"conjs   (eqn e1 e2) = {(eqn e1 e2)}\" |
\"conjs   ( andForm f1 f2) =(   (conjs   f1 ) \\<union>  (conjs   f2 ))\"|
\"conjs   (neg f1 ) = {( neg (   f1 ))}\"|
\"conjs   (orForm f1 f2) ={(orForm  (  f1 )   (  f2 ))}\"|
\"conjs   (implyForm f1 f2) ={ (implyForm  (  f1 )  (  f2 ))}\"|
\"conjs  chaos={}\"

primrec conjsOnVars::\"formula \\<Rightarrow> varType set \\<Rightarrow>formula\" where

\"conjsOnVars   (eqn e1 e2) vars= (if ((varOfExp e1) \\<subseteq> vars) then  (eqn e1 e2) else chaos)\" |
\"conjsOnVars   ( andForm f1 f2) vars = (if (conjsOnVars f1 vars)=chaos then  (conjsOnVars   f2  vars)
                            else if (conjsOnVars f1 vars)=chaos then  (conjsOnVars f1 vars)
                            else  andForm (conjsOnVars f1 vars) (conjsOnVars f2 vars))\"|
\"conjsOnVars   (neg f1 ) vars=  (if ((varOfForm f1) \\<subseteq> vars) then  (neg f1) else chaos)\"|
\"conjsOnVars   (orForm f1 f2) vars=(orForm  (  f1 )   (  f2 ))\"|
\"conjsOnVars   (implyForm f1 f2) vars= (implyForm  (  f1 )  (  f2 ))\"|
\"conjsOnVars   chaos vars= chaos\"

definition preStateEnable::\" statement \\<Rightarrow> formula \\<Rightarrow> formula\\<Rightarrow>bool\" where
\"preStateEnable S post preCond \\<equiv> \\<forall> s. formEval post (trans S s) \\<longrightarrow>  formEval preCond  s \"

definition ofImplyForm::\"formula \\<Rightarrow> bool\" where
\"ofImplyForm f\\<equiv> \\<exists>ant cons. f= implyForm ant cons\"

lemma downNIsNotEmpty:
  \"\\<exists> j xs. down N= j#xs\" (is \"?P N\")
  proof(induct_tac N,auto)
qed   


lemma lemmaOnConjsOnVars:
  \" formEval f s \\<longrightarrow>  formEval (conjsOnVars f S) s \"
  apply(induct_tac f)
  apply force+
  done
lemma noEffectOnExpAux: 
  shows \"(\\<forall>   s. (varOfExp E) \\<inter>  set (map fst asgns) ={} \\<longrightarrow>
  expEval E  s  =  expEval E (transAux asgns s))
  \\<and>
  (\\<forall>   s. (varOfForm f) \\<inter>  set (map fst asgns) ={} \\<longrightarrow>
  formEval f s  =  formEval f (transAux asgns s))\"
  (is \"(\\<forall>  s. ?P asgns s E) \\<and>( \\<forall>  s. ?Q asgns s f)\")
proof(induct_tac E and f)

  fix varType
  let ?E=\"IVar varType\"
  show \"(\\<forall>  s. ?P asgns s ?E)\" (is \"\\<forall>s. ?R s asgns\")
  proof(rule allI)
  fix s
  show \"?R s asgns\"
  proof( induct_tac asgns)
    show \"?R s []\" by simp
    next  
    fix a asgns  
    assume  a1:\"?R s asgns\"
    show \"?R s (a#asgns)\"    
    proof 

    assume c1:\" varOfExp (?E) \\<inter> set (map fst (a # asgns)) = {}\"

      have d1:\"\\<exists> v val0. a=(v,val0)\"
            by auto 
    then obtain var val0 where d2:\"a=(var,val0)\"
            by blast
    (*have b1':\"(\\<forall> f s. ?P asgns s f)\"
          by(cut_tac b1,simp)*)
     have f1:\"expEval ?E s = expEval ?E (transAux ( asgns) s)\"
          
          apply(cut_tac a1  c1 )
          apply auto
          done
      have f2:\" expEval ?E (transAux (a # asgns) s)= expEval ?E (transAux ( asgns) s)\"
          apply(cut_tac a1 c1,simp)
          apply( auto)
         done
      show \" expEval ?E s = expEval ?E (transAux (a # asgns) s)\"
         apply(cut_tac f1 f2, simp)
         done
     qed
   qed
  qed
next
  fix n
  
  let ?E=\"Const n\"
  show \"(\\<forall>  s. ?P asgns s ?E)\" (is \"\\<forall>s. ?R s asgns\")  
  by auto
next
  fix frm e1 e2 
   let ?E=\"iteForm frm e1 e2\"
  assume a1:\"( \\<forall>  s. ?Q asgns s frm)\" and a2:\"(\\<forall>  s. ?P asgns s e1)\" and a3:\"(\\<forall>  s. ?P asgns s e2)\"
  
  show \"(\\<forall>  s. ?P asgns s ?E)\" (is \"\\<forall>s. ?R s asgns\")  
  proof(rule allI,rule impI)
  fix s
   assume c1:\" varOfExp (?E) \\<inter> set (map fst ( asgns)) = {}\"
   show \"expEval (iteForm frm e1 e2) s = expEval (iteForm frm e1 e2) (transAux asgns s)\"
   apply(cut_tac a1 a2 a3 c1)
   apply auto
   done
   qed  
next
  fix e1 e2
  let ?f=\"eqn e1 e2\"
  assume a1:\"(\\<forall>  s. ?P asgns s e1)\" and a2:\"(\\<forall>  s. ?P asgns s e2)\"
  
  show \"(\\<forall>  s. ?Q asgns s ?f)\" (is \"\\<forall>s. ?R s asgns\")  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) 
  qed
next
  fix f1 f2
  let ?f=\"andForm f1 f2\"
  assume a1:\"( \\<forall>  s. ?Q asgns s f1)\" and  a2:\"( \\<forall>  s. ?Q asgns s f2)\"
  show \"( \\<forall>  s. ?Q asgns s ?f)\"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) 
  qed
next
  fix f1 
  let ?f=\"neg f1 \"
  assume a1:\"( \\<forall>  s. ?Q asgns s f1)\"
  show \"( \\<forall>  s. ?Q asgns s ?f)\"
  
  proof(rule allI,rule impI,cut_tac a1 ,auto) 
  qed
next
  fix f1 f2
  let ?f=\"orForm f1 f2\"
  assume a1:\"( \\<forall>  s. ?Q asgns s f1)\" and  a2:\"( \\<forall>  s. ?Q asgns s f2)\"
  show \"( \\<forall>  s. ?Q asgns s ?f)\"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) qed
next
fix f1 f2
  let ?f=\"implyForm f1 f2\"
  assume a1:\"( \\<forall>  s. ?Q asgns s f1)\" and  a2:\"( \\<forall>  s. ?Q asgns s f2)\"
  show \"( \\<forall>  s. ?Q asgns s ?f)\"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) qed
next
  show \"( \\<forall>  s. ?Q asgns s chaos)\"
  by auto
qed
section{*lemmas on varsOf*}
lemma varsOfSent1:
  \" (varOfSent S) = set (map fst (statement2Assigns S))\"
  proof(induct_tac S,auto) qed


 
lemma varsOnCat[simp]:
  shows \"varOfSent (cat S1 S2)=(varOfSent S1 ) \\<union> (varOfSent S2 )\"
  apply(induct_tac S1)
apply (metis (lifting) cat1 varOfSent.simps(1) varOfSent.simps(2))
by (metis Un_assoc cat2 varOfSent.simps(2))
  

lemma   forallVars:
  assumes a1:\"\\<forall> i.( varOfSent (paraForm i))\\<inter> varSet ={}\"
   shows  \"(varOfSent (forallSent (down N) paraForm))\\<inter> varSet ={}\"
  proof(induct_tac N)
    show \" varOfSent (forallSent (down 0) paraForm) \\<inter> varSet = {}\"
      apply(cut_tac a1,force) 
      done
  next
    fix n
    assume b1:\"varOfSent (forallSent (down n) paraForm) \\<inter> varSet = {}\"
    have \" (varOfSent (forallSent (down (Suc n)) paraForm) )  =
      (varOfSent ( paraForm (Suc n)) ) \\<union>
      (varOfSent (forallSent (down  n ) paraForm) )\"
      by (metis (hide_lams, no_types) add_0_right moreSent down.simps(1) down.simps(2) nat.exhaust varsOnCat)
      then show \"  varOfSent (forallSent (down (Suc n)) paraForm) \\<inter> varSet = {}\"
      apply(-,cut_tac a1,simp )
      by (metis (lifting) Int_Un_distrib2 Un_empty_left b1) 
  qed

lemma   forallVars1[simp,intro!]:
  assumes a1:\"\\<forall>i. v \\<notin>( varOfSent (paraForm i))\"
   shows  \"v \\<notin>(varOfSent (forallSent (down N) paraForm))\" (is \"?P N\")
  proof(induct_tac N)
    show \"?P 0\"
      apply(cut_tac a1,force) 
      done
  next
    fix n
    assume b1:\"?P n\"
    have \" (varOfSent (forallSent (down (Suc n)) paraForm) )  =
      (varOfSent ( paraForm (Suc n)) ) \\<union>
      (varOfSent (forallSent (down  n ) paraForm) )\"
      by (metis (hide_lams, no_types) add_0_right moreSent down.simps(1) down.simps(2) nat.exhaust varsOnCat)
      then show \"?P (Suc n) \"
      apply(-,cut_tac a1,simp )
      by (metis (lifting) b1)
  qed
      
lemma varsOfForallSentIn[simp]:
  \"i \\<le>N \\<longrightarrow>v \\<in> varOfSent (paraForm i) \\<longrightarrow> v \\<in> varOfSent (forallSent (down N) paraForm)\" ( is \"?P N\")
proof(induct_tac N)
  show \"?P 0\"
   by auto
   next
    fix N
   assume a1:\"?P N\" 
   show \"?P (Suc N)\"
   proof(rule impI)+
    (*have b0:\"forallSent (Suc N # down ( N)) paraForm=cat (paraForm (Suc N)) (forallSent ( down ( N)) paraForm)\" thm moreSent
       apply(rule moreSent)*)
    assume b0:\"i \\<le> Suc N\" and b1:\"  v \\<in> varOfSent (paraForm i)\"  
    have b2:\"  varOfSent  (forallSent (down (Suc N)) paraForm) = varOfSent (paraForm (Suc N)) \\<union>   varOfSent (forallSent (down N) paraForm)\"
     by (metis down.simps(2) downNIsNotEmpty paraTheory.moreSent varsOnCat) 
     have \"i \\<le> N | i=Suc N\" by(cut_tac b0,auto)
    moreover
    {assume c1:\"i \\<le> N\"
     have c2:\" v \\<in>varOfSent (forallSent (down N) paraForm)\" 
     apply(cut_tac c1 b1 a1,auto) done
     then have \"v \\<in> varOfSent (forallSent (down (Suc N)) paraForm)\" by(cut_tac c1 c2 b2,auto)
     }
     moreover
    {assume c1:\"i =Suc N\"
     from c1  have \"v \\<in> varOfSent (forallSent (down (Suc N)) paraForm)\" by(cut_tac c1 b1 b2,auto) 
     }
    ultimately show \"v \\<in> varOfSent (forallSent (down (Suc N)) paraForm)\" by blast
  qed
  qed
     
lemma noEffect: shows \"(\\<forall>   s. (varOfExp E) \\<inter>  (varOfSent S) ={} \\<longrightarrow> expEval E s  =  expEval E (trans S s)) \\<and> 
(\\<forall>s. varOfForm f \\<inter>  (varOfSent S) ={}\\<longrightarrow>
         formEval f s = formEval f (trans S s))\"
apply(cut_tac  f=\"f\" and E=\"E\" and asgns=\"  ((statement2Assigns S))\" in noEffectOnExpAux) 
apply(unfold trans_def)
apply(cut_tac S=\"S\" in varsOfSent1)
apply metis
done

lemma noEffectOnExp: 
  assumes a1:\"(varOfExp E) \\<inter>  (varOfSent S) ={} \"
    shows \" expEval E s  =  expEval E (trans S s)\"
by (metis assms noEffect) 


lemma noEffectOnFormula: 
  assumes a1:\"(varOfForm f) \\<inter>  (varOfSent S) ={} \"
    shows \" formEval f s  =  formEval f (trans S s)\"
by (metis assms noEffect) 

lemma conjsOfConj: \"\\<not> (andForm f1 f2)  \\<in> conjs f\"
  apply(induct_tac f)
  apply auto
  done

lemma inConjsInply:
  shows \"f \\<in> conjs f'\\<longrightarrow>formEval f' s \\<longrightarrow> formEval f s\"
  apply(induct_tac f')
  apply force+
  done

primrec mutualNeg::\"formula \\<Rightarrow>formula\" where


\"mutualNeg (eqn e1 e2) = neg (eqn e1 e2) \" |
\"mutualNeg ( andForm f1 f2) = neg  ( andForm f1 f2)\"|
\"mutualNeg (neg f1 ) = ( ( f1 ))\"|
\"mutualNeg (orForm f1 f2) = neg (orForm f1 f2 )\"|
\"mutualNeg (implyForm f1 f2) = neg  (implyForm f1 f2)\" |
\"mutualNeg chaos=chaos\"
  
primrec dual::\"formula \\<Rightarrow> formula\" where
\"dual (implyForm f g)=  (implyForm (mutualNeg  g) (mutualNeg  f))\"

definition logicImply::\"formula \\<Rightarrow> formula \\<Rightarrow>bool\" where [simp]:
\"logicImply f1 f2\\<equiv>  ( \\<forall> s. formEval f1 s\\<longrightarrow> formEval f2 s)\"



  

primrec valOf::\"assignType list \\<Rightarrow> varType =>expType\"  where
\"valOf [] v=IVar v\" |
\"valOf (x#xs) v= (if ((fst x) =v) then (snd x) else valOf xs v)\"

primrec substExp :: \"expType\\<Rightarrow> assignType list \\<Rightarrow>expType\"  and 
substForm ::\"formula \\<Rightarrow> assignType list \\<Rightarrow> formula\" where 
(*substExpVar: \"substExp  (IVar v') asgns= (if ( \\<not>wellformedAssgnList asgns ) then (IVar v')
                             else if (v' \\<in> set (map fst asgns)) then  (valOf  asgns v') else (IVar v'))\" |*)

substExpVar: \"substExp  (IVar v') asgns=   (valOf  asgns v')  \"| 

substExpConst: \"substExp  (Const i)  asgns= Const i\" |

substExpite: \"substExp  (iteForm f e1 e2)  asgns= (iteForm (substForm f asgns) (substExp e1  asgns) (substExp e2  asgns))\"| 
\"substForm (eqn l r)  asgns=(eqn (substExp l  asgns) (substExp r  asgns))\"  |
\"substForm ( andForm f1 f2)  asgns =   ( andForm (substForm f1  asgns)  (substForm f2  asgns))\"|
\"substForm (neg f1 )   asgns= (neg ( substForm f1  asgns ))\"|
\"substForm (orForm f1 f2)   asgns= ( orForm (substForm f1  asgns )  (substForm f2  asgns))\"|
\"substForm (implyForm f1 f2)   asgns= (implyForm (substForm f1 asgns)  (substForm f2  asgns))\" |
\"substForm  chaos   asgns=chaos\"

definition  substExpByStatement ::\"expType \\<Rightarrow>statement \\<Rightarrow>expType\"   where [simp]:
\"substExpByStatement e S\\<equiv>substExp e (statement2Assigns S)\" 

definition substFormByStatement ::\"formula \\<Rightarrow>statement \\<Rightarrow>formula\"   where [simp]:
\"substFormByStatement f S\\<equiv>substForm f (statement2Assigns S)\" 


definition statementEnableForm::\"rule \\<Rightarrow> formula\\<Rightarrow>bool\" where  [simp]:
\" statementEnableForm  r f \\<equiv>
  \\<forall>s. formEval (pre r) s \\<longrightarrow> formEval  (substFormByStatement f (act r)) s\"

definition statementDisableForm::\"rule  \\<Rightarrow> formula \\<Rightarrow> bool\" where  [simp]:
\" statementDisableForm r f \\<equiv>
     \\<forall>s. formEval (pre r) s \\<longrightarrow> \\<not> formEval  (substFormByStatement f (act r)) s \"


(*primrec invHoldForRule1::\" formula \\<Rightarrow> rule \\<Rightarrow> bool\" where
\"invHoldForRule1 (implyForm ant cons) r=   
  ((statementEnableForm ( r) cons) \\<or>  (statementDisableForm ( r) ant) ) \"*)

primrec invHoldForRule1::\" formula \\<Rightarrow> rule \\<Rightarrow> bool\" where
\"invHoldForRule1 (implyForm ant cons) r=   
 ( \\<forall>s. formEval (pre r) s \\<longrightarrow>  formEval  (substFormByStatement  (implyForm ant cons) (act r)) s )\"


primrec  invHoldForRule3::\"formula \\<Rightarrow> rule \\<Rightarrow>formula set\\<Rightarrow> bool\"  where
\" invHoldForRule3 (implyForm ant cons) r fs = (( (varOfSent (act r)) \\<inter> varOfForm cons={})\\<and>
  ( \\<exists>f'  ant'. f' \\<in> fs \\<and> logicImply f'  (implyForm ant' cons ) \\<and> 
  (logicImply (andForm (pre r)  (substFormByStatement (ant) (act r)))  ant')))\"




primrec  invHoldForRule4::\"formula \\<Rightarrow> rule \\<Rightarrow>formula set\\<Rightarrow> bool\"  where
\" invHoldForRule4 (implyForm ant cons) r fs = (

  ( \\<exists>f'  ant'  ant''. f' \\<in> fs \\<and> logicImply f'  (implyForm ant' (neg ant'') ) \\<and>  ( (varOfSent (act r)) \\<inter> varOfForm ant''={})\\<and> logicImply ant ant'' \\<and>
              ( logicImply (andForm  (pre r)  (substFormByStatement (neg cons) (act r))) ant'))
)\"

(*thm noEffect
lemma noEffect0:
  assumes a1:\" (varOfSent S) \\<inter> (varOfForm f)={} \" and a2:\"formEval f s\"
  shows \"formEval f (trans S s)\"
  by (metis a1 a2 noEffect)*)



definition invHoldForRule5::\"formula \\<Rightarrow> rule \\<Rightarrow>formula set  \\<Rightarrow>bool\" where  [simp]:
 \"invHoldForRule5 inv0 r fs \\<equiv>
 ( \\<exists>f'.  f' \\<in> fs \\<and> logicImply f' (substFormByStatement inv0 (act r) ))\"


abbreviation invHoldForRule::\"formula \\<Rightarrow> rule \\<Rightarrow> (formula set) \\<Rightarrow> bool\" where
  \"invHoldForRule inv0 r invs \\<equiv>
  invHoldForRule1 inv0 r \\<or>  invHoldForRule2 inv0 r \\<or>
   invHoldForRule3 inv0 r invs \\<or> invHoldForRule4 inv0 r invs \\<or> invHoldForRule5 inv0 r invs\"

definition consistent::\"formula set \\<Rightarrow> formula set \\<Rightarrow> rule set \\<Rightarrow>bool\"  where
\"consistent invs inis rs \\<equiv>
(\\<forall>inv ini s. (inv \\<in> invs \\<longrightarrow> ini\\<in> inis\\<longrightarrow> formEval ini s \\<longrightarrow> formEval inv s)) \\<and>
 (\\<forall> inv r.  (inv \\<in>invs  \\<longrightarrow> r \\<in> rs \\<longrightarrow> invHoldForRule inv r invs  ))\"



lemma  preCondOnExp:
  
  shows \"( ( expEval (substExpByStatement e S) s =expEval e (trans S s)) \\<and>
           ( formEval (substFormByStatement f S) s = formEval f (trans S s)))\"
           
    (is \"((  ?LHS e S=?RHS e S)\\<and> ( ?LHS1 f S=?RHS1 f S))\")
  proof(induct_tac e and f)
      fix v
      let ?e=\"(IVar v)\"
      show  \"?LHS ?e S=?RHS ?e S\"
      proof(induct_tac S)
        fix prod
        let ?S=\"assign prod\"
        show \"?LHS ?e ?S=?RHS ?e ?S\"
        
        apply(unfold  substExpByStatement_def trans_def,auto)
        done
    next
       fix prod S
       let ?S=\"parallel prod S\"
       assume b1:\"?LHS ?e S=?RHS ?e S\"
       
       show \"?LHS ?e ?S=?RHS ?e ?S\"
       
       proof(unfold  substExpByStatement_def trans_def,
       case_tac \"fst prod =v\",force)
       assume d1:\"fst prod \\<noteq> v \"
       show \"expEval (substExp (IVar v) (statement2Assigns (parallel prod S))) s =
              expEval (IVar v) (transAux (statement2Assigns (parallel prod S)) s)\"
       proof(cut_tac d1,simp,case_tac \"(varOfExp ?e) \\<inter>  set (map fst (statement2Assigns S) )={}\")
        assume e1:\"(varOfExp ?e) \\<inter>  set (map fst (statement2Assigns S) )={}\"
        have f1:\"v \\<notin> fst ` set (statement2Assigns S)\"
        apply(cut_tac e1,simp)
        done
        have f2:\" expEval ?e s  =  expEval ?e (transAux (statement2Assigns S) s)\"
          apply(cut_tac e1)
          by (metis (no_types) noEffectOnExpAux)

        show \" expEval (valOf (statement2Assigns S) v) s = transAux (statement2Assigns S) s v\"
        using b1 by auto
        
        next
        assume  e1:\"(varOfExp ?e) \\<inter>  set (map fst (statement2Assigns S) )\\<noteq>{}\"
        have f1:\"v \\<in> fst ` set (statement2Assigns S)\"
        apply(cut_tac e1,simp)
        done
      show \" expEval (valOf (statement2Assigns S) v) s = transAux (statement2Assigns S) s v\"
        using b1 by auto 
      qed 
    qed
  qed
next 
  fix n
  let ?e=\"(Const n)\"
      show  \"?LHS ?e S=?RHS ?e S\"
      apply( simp)
      done
next
  fix f e1 e2
  assume a1:\" ( ?LHS1 f S=?RHS1 f S)\" and
  a2:\"?LHS e1 S=?RHS e1 S\" and a3:\"?LHS e2 S=?RHS e2 S\"
  let ?e=\"iteForm f e1 e2\"
  show \"?LHS ?e S=?RHS ?e S\"
  using a1 a2 a3 by auto
next
  fix e1 e2
  
  assume a1:\"?LHS e1 S=?RHS e1 S\" and a2:\"?LHS e2 S=?RHS e2 S\"
  let ?f=\"eqn e1 e2\"
  show \"( ?LHS1 ?f S=?RHS1 ?f S)\"
   using a1 a2 by auto 
next
  fix f1 f2
  assume a1:\" ( ?LHS1 f1 S=?RHS1 f1 S)\" and  a2:\" ( ?LHS1 f2 S=?RHS1 f2 S)\"
  let ?f=\"andForm f1 f2\"
  
  show \"( ?LHS1 ?f S=?RHS1 ?f S)\"
   using a1 a2 by auto  
next
  fix f1
  assume a1:\" ( ?LHS1 f1 S=?RHS1 f1 S)\"
  let ?f=\"neg f1\"
  show \"( ?LHS1 ?f S=?RHS1 ?f S)\"
   using a1 by auto
next   
  fix f1 f2
  assume a1:\" ( ?LHS1 f1 S=?RHS1 f1 S)\" and  a2:\" ( ?LHS1 f2 S=?RHS1 f2 S)\"
  let ?f=\"implyForm f1 f2\"
  
  show \"( ?LHS1 ?f S=?RHS1 ?f S)\"
  using a1 a2 by auto
next
  fix f1 f2
  assume a1:\" ( ?LHS1 f1 S=?RHS1 f1 S)\" and  a2:\" ( ?LHS1 f2 S=?RHS1 f2 S)\"
  let ?f=\"orForm f1 f2\"
  
  show \"( ?LHS1 ?f S=?RHS1 ?f S)\"
  using a1 a2 by auto
next
  let ?f=\"chaos\"
  show \"( ?LHS1 ?f S=?RHS1 ?f S)\"
  by auto
qed



lemma consistentLemma:
  assumes a1:\"consistent invs inis rs\" and a2:\"s \\<in> reachableSet inis rs\" and
  a3:\"\\<forall>inv. inv \\<in> invs \\<longrightarrow> ofImplyForm inv\"
  shows \"\\<forall> inv. inv \\<in> invs \\<longrightarrow>formEval inv s\"  (is \"?P s\")
  using a2
  proof induct
    case (initState ini s)
    show \"?P s\"
      apply(cut_tac a1, unfold consistent_def)
      by (metis (lifting) initState(1) initState(2))
  next
    case (oneStep s r)
    show \"?P  (trans (act r) s)\"    
    proof (rule allI, rule impI)
      fix inv
      assume b1:\"inv \\<in> invs\"
      have b2:\"invHoldForRule5 inv r invs \\<or> invHoldForRule4 inv r invs \\<or> invHoldForRule3 inv r invs \\<or> invHoldForRule2 inv r \\<or> invHoldForRule1 inv r\"
        apply(cut_tac a1, unfold consistent_def)
        by (metis b1 oneStep(3))

       moreover
      {assume b1':\"invHoldForRule5  inv r invs\"
        
        have b2:\"\\<exists> ant cons. inv=implyForm ant cons\"
          by(cut_tac b1 a3, unfold ofImplyForm_def,auto)

        then obtain ant cons where b2':\"inv=implyForm ant cons\"
          by auto

        

        have b3:\" \\<exists> f'. f' \\<in> invs \\<and> logicImply f' (substFormByStatement inv (act r) ) \"  (is \"\\<exists> f'.  ?P f' \")
           apply (cut_tac b1' b2', unfold invHoldForRule5_def,auto)
          done

        then obtain f' ant' where b3':\"?P f'  \"
          by blast

        have b4:\" formEval f' s\"
          apply(cut_tac b3' )
          by (metis (no_types) oneStep(2))

        have b5:\"formEval  (substFormByStatement inv (act r))  s\"
          by (metis (no_types) b3' b4 logicImply_def)
          
        then have \"formEval inv (trans (act r) s)\"
        by (metis preCondOnExp)
        
      }
          
      moreover
      {assume b1':\"invHoldForRule3 inv r invs\"
        
        have b2:\"\\<exists> ant cons. inv=implyForm ant cons\"
          by(cut_tac b1 a3, unfold ofImplyForm_def,auto)

        then obtain ant cons where b2':\"inv=implyForm ant cons\"
          by auto

        

        have b3:\"  ( \\<exists>f'  ant'. f' \\<in> invs \\<and> logicImply f'  (implyForm ant' cons ) \\<and> 
          (logicImply (andForm (pre r)  (substFormByStatement (ant) (act r)))  ant'))\"  (is \"\\<exists> f' ant'. ?P f' ant'\")
           apply (cut_tac b1' b2', unfold invHoldForRule3_def,auto)
          done

        then obtain f' ant' where b3':\"?P f' ant' \"
          by blast

        have b4:\" formEval f' s\"
          apply(cut_tac b3' )
          by (metis (no_types) oneStep(2))

        have b5:\"formEval (pre r) s\"
          by (metis (lifting) oneStep(4))

        have b6:\"formEval (substFormByStatement (ant) (act r)) s \\<or>
          \\<not>formEval (substFormByStatement (ant) (act r)) s\"
          by blast
        moreover
        {assume b7:\"formEval (substFormByStatement (ant) (act r)) s\"
          have b8:\"formEval ant' s\"
            apply(cut_tac b5 b7)
            apply(cut_tac b3',simp add:logicImply_def)
            done
          have b9:\"formEval cons  s\"
            by (metis (full_types) b3' b4 b8 evalImp logicImply_def)
          thm noEffect  
          have b10:\" formEval cons (trans (act r) s)\"
          by (metis Int_commute b1' b2' b9 invHoldForRule3.simps noEffectOnFormula)

          have \"formEval inv (trans (act r) s)\"
            apply(cut_tac b10 b2',force)
            done
        }
        moreover
        {assume b4':\"\\<not>formEval (substFormByStatement (ant) (act r)) s\"
          have b5:\"\\<not>formEval (ant) (trans (act r) s)\"
            apply(cut_tac  b4')
            by (metis preCondOnExp)
      
          have \"formEval inv (trans (act r) s)\"
            by(cut_tac b5 b2', unfold trans_def, auto)
        }
        ultimately have \"formEval inv (trans (act r) s)\" 
          by blast
      }
      moreover
      {assume b1':\"invHoldForRule2 inv r \"
        have b2:\"formEval inv s\"
        by (metis b1 oneStep.hyps(2))
        have \"formEval inv (trans (act r) s)\"
        by (metis b1' b2 inf_commute invHoldForRule2_def noEffect)
          (*  apply(rule noEffect0)
          apply(cut_tac b1')
          apply (metis invHoldForRule2_def)
          by(metis b2)*)
      }
      moreover
      {assume b1':\"invHoldForRule1 inv r \"
         
        have b2:\"\\<exists> ant cons. inv=implyForm ant cons\"
          by(cut_tac b1 a3, unfold ofImplyForm_def,auto)
        have b3:\"formEval (pre r) s\"
          by (metis (lifting) oneStep(4))

        from b2 obtain ant cons where b2':\"inv=implyForm ant cons\"
           by auto
         have \"formEval inv (trans (act r) s)\"
           apply(subgoal_tac \"formEval (substFormByStatement inv (act r)) s\")
           apply (metis preCondOnExp)
           apply(cut_tac b1' b2')
           
           apply(cut_tac b3) by auto
          
        

        
       }
       moreover
       {assume b1':\"invHoldForRule4 inv r invs\"
        
         have b2:\"\\<exists> ant cons. inv=implyForm ant cons\"
           by(cut_tac b1 a3, unfold ofImplyForm_def,auto)

         then obtain ant cons where b2':\"inv=implyForm ant cons\"
           by auto

         

        
         have b3:\"
  ( \\<exists>f'  ant'  ant''. f' \\<in> invs \\<and> logicImply f'  (implyForm ant' (neg ant'') ) \\<and>  ( (varOfSent (act r)) \\<inter> varOfForm ant''={})\\<and> logicImply ant ant'' \\<and>
              ( logicImply (andForm  (pre r)  (substFormByStatement (neg cons) (act r))) ant'))\" (is \" ( \\<exists>f' ant' ant''. ?P f' ant' ant'')\")
           apply(cut_tac b1' b2')
           
           apply (simp)
           done

         then obtain f' and ant' and ant''  where b3':\"(?P f' ant' ant'')\"
           by blast

      

        
         have b4':\"formEval (substFormByStatement (neg cons) (act r)) s \\<or>
             \\<not>formEval (substFormByStatement (neg cons) (act r)) s\"
           by blast
         moreover
         {assume b4':\"formEval (substFormByStatement (neg cons) (act r)) s\"
           have b5:\"formEval ant' s\"
             apply(cut_tac b3' b4')
             by (metis (no_types) evalAnd logicImply_def oneStep(4))
           have b6:\"\\<not>formEval ant'' s\"
           
            by (smt b3' b5 evalImp evalNeg logicImply_def oneStep(2))

          
           
      
           have b8:\"\\<not> formEval ant'' (trans (act r) s)\"
           by (metis Int_commute b3' b6 noEffectOnFormula)

            have b7:\"\\<not>formEval ant  (trans (act r) s)\"
              by (metis b3' b8 logicImply_def)

           have \"formEval inv (trans (act r) s)\"
             apply(cut_tac b7 b2',force)
             done
         }
         moreover
         {assume b4':\"\\<not>formEval (substFormByStatement (neg cons) (act r)) s\"
           have \"\\<not>formEval (neg cons) (trans (act r) s)\"
             apply(cut_tac  b4')
             by (metis preCondOnExp)
         
           then have b5: \"formEval ( cons) (trans (act r) s)\"
             by auto
           have \"formEval inv (trans (act r) s)\"
             by(cut_tac b5 b2', unfold trans_def, auto)
         }
         ultimately have \"formEval inv (trans (act r) s)\" 
           by blast
       }
       ultimately show \"formEval inv (trans (act r) s)\"
         by blast
     qed
   qed      



definition invHoldForRule1'::\" state \\<Rightarrow> formula \\<Rightarrow> rule \\<Rightarrow> bool\" where [simp]:
\"invHoldForRule1' s f  r \\<equiv>  
 (  formEval (pre r) s \\<longrightarrow>  formEval  (substFormByStatement f  (act r)) s )\"

 definition invHoldForRule2'::\" state \\<Rightarrow> formula \\<Rightarrow> rule \\<Rightarrow> bool\" where [simp]:
\"invHoldForRule2' s f  r \\<equiv>  (  formEval  (substFormByStatement f  (act r)) s  =  formEval f s)\"

definition  invHoldForRule3'::\"state \\<Rightarrow> formula \\<Rightarrow> rule \\<Rightarrow>formula set\\<Rightarrow> bool\"  where [simp]:
\" invHoldForRule3' s f r fs  \\<equiv>  
  (let pref=substFormByStatement f (act r) in
  ( \\<exists>f'. f' \\<in> fs \\<and>  (formEval   (andForm (pre r)  f') s\\<longrightarrow> formEval  pref s)))\"
  
primrec andListForm::\"formula list \\<Rightarrow> formula \" where
\"andListForm [] = chaos\" |
\"andListForm  (f#fs) = andForm f (andListForm  fs)\"

definition andSetForm::\"formula set \\<Rightarrow> formula \" where
\"andSetForm fs == Finite_Set.fold  andForm chaos  fs\"
  
definition  invHoldForRule3''::\"state \\<Rightarrow> formula \\<Rightarrow> rule \\<Rightarrow>formula set\\<Rightarrow> bool\"  where [simp]:
\" invHoldForRule3'' s f r fs  \\<equiv>  
  (let pref=substFormByStatement f (act r) in
  ( (\\<forall> f'.  f' \\<in>  fs\\<longrightarrow>formEval f'  s) \\<longrightarrow>formEval (pre r)  s\\<longrightarrow> formEval  pref s))\" 


abbreviation invHoldForRule'::\"state \\<Rightarrow>formula \\<Rightarrow> rule \\<Rightarrow> (formula set) \\<Rightarrow> bool\" where
  \"invHoldForRule' s inv0 r invs \\<equiv>
    invHoldForRule1' s inv0 r \\<or>  invHoldForRule2' s inv0 r \\<or>
   invHoldForRule3' s inv0 r invs \"

abbreviation invHoldForRule''::\"state \\<Rightarrow> formula \\<Rightarrow> rule \\<Rightarrow> (formula set) \\<Rightarrow> bool\" where
  \"invHoldForRule'' s inv0 r invs \\<equiv>
    invHoldForRule1' s inv0 r \\<or>  invHoldForRule2' s inv0 r \\<or>
   invHoldForRule3'' s inv0 r invs \"   
   
lemma weak3:
 \" invHoldForRule3' s f r fs \\<Longrightarrow> invHoldForRule3'' s f r fs \"
  by auto
  
lemma weak:
 \" invHoldForRule' s f r fs \\<Longrightarrow> invHoldForRule'' s f r fs \"
  by( auto intro:weak3)  
  
lemma strengthEn:
\" invHoldForRule'' s f r fs \\<Longrightarrow> invHoldForRule' s f r fs \"
  by( auto )  

definition newconsistent::\"formula set \\<Rightarrow> formula set \\<Rightarrow> rule set \\<Rightarrow>bool\"  where
\"newconsistent invs inis rs \\<equiv>
(\\<forall>inv ini s. (inv \\<in> invs \\<longrightarrow> ini\\<in> inis\\<longrightarrow> formEval ini s \\<longrightarrow> formEval inv s)) \\<and>
 (\\<forall> inv r s.  (inv \\<in>invs  \\<longrightarrow> r \\<in> rs \\<longrightarrow> invHoldForRule' s inv r invs  ))\"   
 
 definition newconsistent'::\"formula set \\<Rightarrow> formula set \\<Rightarrow> rule set \\<Rightarrow>bool\"  where
\"newconsistent' invs inis rs \\<equiv>
(\\<forall>inv ini s. (inv \\<in> invs \\<longrightarrow> ini\\<in> inis\\<longrightarrow> formEval ini s \\<longrightarrow> formEval inv s)) \\<and>
 (\\<forall> inv r s.  (inv \\<in>invs  \\<longrightarrow> r \\<in> rs \\<longrightarrow> invHoldForRule'' s inv r invs  ))\"   
 

lemma newconsistentLemma:
  assumes a1:\"newconsistent invs inis rs\" and a2:\"s \\<in> reachableSet inis rs\" 
  shows \"\\<forall> inv. inv \\<in> invs \\<longrightarrow>formEval inv s\"  (is \"?P s\")
  using a2
  proof induct
    case (initState ini s)
    show \"?P s\"
      apply(cut_tac a1, unfold newconsistent_def)
      by (metis (lifting) initState(1) initState(2))
  next
    case (oneStep s r)
    show \"?P  (trans (act r) s)\"    
    proof (rule allI, rule impI)
      fix inv
      assume b1:\"inv \\<in> invs\"
      have b2:\" invHoldForRule3' s inv r  invs \\<or> invHoldForRule2' s inv r   \\<or> invHoldForRule1' s inv r  \"
        apply(cut_tac a1, unfold newconsistent_def)
        by (metis b1 oneStep(3))
        
     moreover
      {   assume c1:\"invHoldForRule3' s inv r invs\"
        
        let ?pref=\"substFormByStatement inv (act r)\"
          have b3:\"  ( (\\<forall> f'.  f' \\<in>  invs\\<longrightarrow>formEval f'  s) \\<longrightarrow>formEval (pre r)  s\\<longrightarrow> formEval  ?pref s)  \"  (is \" ?P fs \")
           apply (cut_tac c1, unfold invHoldForRule3'_def,auto)
          done

        then have b3':\"?P fs  \"
          by blast

        have b4:\" (\\<forall> f'.  f' \\<in>  invs\\<longrightarrow>formEval f'  s)\"
          apply(cut_tac b3' )
          by (metis (no_types) oneStep(2))

        have b5:\"formEval (pre r) s\"
          by (metis (lifting) oneStep(4))

        have b6:\"formEval ?pref s\"
         by(cut_tac b4 b5 b3', auto simp add:logicImply_def)

          have \"formEval inv (trans (act r) s)\"
            apply(cut_tac b6,metis preCondOnExp)
            done
      }
     
     moreover
      {assume b1':\"invHoldForRule2' s inv r \"
        have b2:\"formEval inv s\"
        by (metis b1 oneStep.hyps(2))
        
        let ?pref=\"substFormByStatement inv (act r)\"
        have b3:\" (  formEval  ?pref s  =  formEval inv s)\"
        by(cut_tac b1',unfold  invHoldForRule2'_def,simp)
        
        with b2 have b4:\"formEval ?pref s\"
          by auto
          
        have \"formEval inv (trans (act r) s)\"
        by (cut_tac b4,  metis preCondOnExp)
          (*  apply(rule noEffect0)
          apply(cut_tac b1')
          apply (metis invHoldForRule2_def)
          by(metis b2)*)
      }
      moreover
      {assume b1':\"invHoldForRule1' s inv r \"
         
         have b5:\"formEval (pre r) s\"
          by (metis (lifting) oneStep(4))
        
         have \"formEval inv (trans (act r) s)\"
           apply(subgoal_tac \"formEval (substFormByStatement inv (act r)) s\")
           apply (metis preCondOnExp)
           apply(cut_tac b1' b5)
           by(unfold invHoldForRule1'_def,auto)
       
       }
       ultimately show \"formEval inv (trans (act r) s)\"
         by blast
     qed
   qed      
lemma andListFormAux1:
 
  shows \"set fs \\<subseteq>  fs' \\<longrightarrow>( \\<forall> inv. inv \\<in> fs' \\<longrightarrow>formEval inv s)\\<longrightarrow> formEval (andListForm fs) s\"
  proof(induct_tac fs,auto)qed
  
lemma andListForm1[simp,intro]:
 
  \"\\<lbrakk>set fs \\<subseteq>  invs ; ( \\<forall> inv. inv \\<in>invs \\<longrightarrow>formEval inv s)\\<rbrakk>\\<Longrightarrow> formEval (andListForm fs) s\"
 by(metis  andListFormAux1)
 
 
(*lemma andListSetAux1:
 
  shows \" fs \\<subseteq>  fs' \\<longrightarrow>( \\<forall> inv. inv \\<in> fs' \\<longrightarrow>formEval inv s)\\<longrightarrow> formEval (andSetForm fs) s\"
  proof(induct_tac fs,auto)qed*)
  
lemma newconsistentLemma':
  assumes a1:\"newconsistent' invs inis rs\" and a2:\"s \\<in> reachableSet inis rs\" 
  shows \"\\<forall> inv. inv \\<in> invs \\<longrightarrow>formEval inv s\"  (is \"?P s\")
  using a2
  proof induct
    case (initState ini s)
    show \"?P s\"
      apply(cut_tac a1, unfold newconsistent'_def)
      by (metis (lifting) initState(1) initState(2))
  next
    case (oneStep s r)
    show \"?P  (trans (act r) s)\"    
    proof (rule allI, rule impI)
      fix inv
      assume b1:\"inv \\<in> invs\"
      have b2:\" invHoldForRule3'' s inv r  invs \\<or> invHoldForRule2' s inv r   \\<or> invHoldForRule1' s inv r  \"
        apply(cut_tac a1, unfold newconsistent'_def)
        by (metis b1 oneStep(3))
        
     moreover
      {   assume c1:\"invHoldForRule3'' s inv r invs\"
        
        let ?pref=\"substFormByStatement inv (act r)\"
           have b3:\"  ( (\\<forall> f'.  f' \\<in>  invs\\<longrightarrow>formEval f'  s) \\<longrightarrow>formEval (pre r)  s\\<longrightarrow> formEval  ?pref s)  \"  (is \" ?P fs \")
           apply (cut_tac c1, unfold invHoldForRule3''_def,auto)
          done
         

        then obtain fs'  where b3':\"?P fs \"
          by blast
          
        
        have b4:\" (\\<forall> f'.  f' \\<in>  invs\\<longrightarrow>formEval f'  s)\"
          apply(cut_tac b3' )
          by (metis (no_types) oneStep(2))

        have b5:\"formEval (pre r) s\"
          by (metis (lifting) oneStep(4))

        have b6:\"formEval ?pref s\"
         by(cut_tac b4 b5 b3', auto simp add:logicImply_def)

          have \"formEval inv (trans (act r) s)\"
            apply(cut_tac b6,metis preCondOnExp)
            done  
      }
     
     moreover
      {assume b1':\"invHoldForRule2' s inv r \"
        have b2:\"formEval inv s\"
        by (metis b1 oneStep.hyps(2))
        
        let ?pref=\"substFormByStatement inv (act r)\"
        have b3:\" (  formEval  ?pref s  =  formEval inv s)\"
        by(cut_tac b1',unfold  invHoldForRule2'_def,simp)
        
        with b2 have b4:\"formEval ?pref s\"
          by auto
          
        have \"formEval inv (trans (act r) s)\"
        by (cut_tac b4,  metis preCondOnExp)
          (*  apply(rule noEffect0)
          apply(cut_tac b1')
          apply (metis invHoldForRule2_def)
          by(metis b2)*)
      }
      moreover
      {assume b1':\"invHoldForRule1' s inv r \"
         
         have b5:\"formEval (pre r) s\"
          by (metis (lifting) oneStep(4))
        
         have \"formEval inv (trans (act r) s)\"
           apply(subgoal_tac \"formEval (substFormByStatement inv (act r)) s\")
           apply (metis preCondOnExp)
           apply(cut_tac b1' b5)
           by(unfold invHoldForRule1'_def,auto)
       
       }
       ultimately show \"formEval inv (trans (act r) s)\"
         by blast
     qed
   qed    
   

lemma forall1:
  shows \"\\<forall> i. i \\<le> N \\<longrightarrow>formEval (forallForm (down N) pf ) s\\<longrightarrow>formEval (pf i) s\" (is \"?P N\")  
proof(induct_tac N)
    show \"?P  0\"
      by simp
  next
    fix N
    assume b1:\"?P N\"
    show \"?P  (Suc N)\"
      proof(case_tac \"N =0\")
        assume c1:\"N=0\"
        show \"?P  (Suc N)\"
        proof(cut_tac c1, auto,case_tac \"i=0\", auto,case_tac \"i=1\",auto)qed
      next
        assume c1:\"N\\<noteq>0\"
        have \"0<N \" 
          by(cut_tac c1, arith)
       then have c2:\"\\<exists> N'. down (Suc N)=(Suc N)#N#down N'\"
         by (metis down.simps(2) gr0_conv_Suc)
       then obtain N' where c2:\"down (Suc N)=(Suc N)#N#down N'\"
         by blast
       then have c3:\"(N#down N')=down N\"
         by simp
       show \"?P  (Suc N)\"      
       proof(rule allI,(rule impI)+,cut_tac c2,simp)
         fix i
         assume d1:\"i\\<le> Suc N\" and d2:\" formEval (pf (Suc N)) s \\<and> formEval (forallForm (N # down N') pf) s\"
         have \"i=Suc N \\<or> i<Suc N\" 
           by (cut_tac d1, arith)
         moreover
         {assume e1:\"i=Suc N\"
           have \" formEval (pf i) s\"
             by (metis (lifting) d2 e1)
         }
         moreover
         {assume e1:\"i<Suc N\"           
           have \" formEval (pf i) s\"
             by (metis b1 c3 d1 d2 le_Suc_eq)
         }
         ultimately show \"formEval (pf i) s\"
           by blast
       qed
     qed
   qed

lemma forallLemma [simp,dest]:
  assumes a1:\"i \\<le> N\" and a2:\"formEval (forallForm (down N) pf ) s\"
  shows \"formEval (pf i) s\"
by (metis a1 a2 forall1)      



primrec antOf ::\"formula \\<Rightarrow> formula\" where [simp]: 
\"antOf (implyForm A B)=A\"

primrec consOf::\"formula \\<Rightarrow> formula\" where [simp] :
\"consOf (implyForm A B)=B\"




lemma subByStatement1:
  assumes a1:\"  x\\<noteq> x' \"
  shows \"wellformedAssgnList (statement2Assigns ((parallel ( x', e) S)) ) \\<longrightarrow>

  substFormByStatement (eqn (IVar  x) (Const n)) (parallel ( x', e) S)=  substFormByStatement  (eqn (IVar x) (Const n)) S\"
  (is \"?P S\")
  (*proof( induct_tac S)
    fix prod
    let ?S=\"assign prod\" 
    show \"?P ?S\"*)
    

  apply(unfold substFormByStatement_def,simp)
  apply( induct_tac S)
  apply(cut_tac a1,unfold wellformedAssgnList_def, simp,auto)
  done


(*lemma subByStatement2[simp]:
  assumes a1:\" x' \\<notin> varOfForm f \"
  shows \"  substFormByStatement f (parallel ( x', e) S)=  substFormByStatement  f S\"
  (is \"?P S\")
  sorry*)


lemma ForallSentForm [simp]:
  shows a1:\" (statement2Assigns (forallSent (down N) 
                                                              (\\<lambda>i. assign
                                                                (Para n i, e' i))))=map (\\<lambda>i. (Para n i, e' i)) (down N)\" (is \"?P N\")
proof(induct_tac N)
  show \"?P 0\"
    apply simp
    done
next
  fix N
  assume b1:\"?P N\"
  show \"?P (Suc N )\"
  proof(cut_tac b1, simp)
    have b2:\"\\<exists> j xs. down N= j#xs\"
      by (metis downNIsNotEmpty) 
  then obtain j xs where b2:\"down N=j#xs\" by blast
    show\"  statement2Assigns (forallSent (Suc N # down N) (\\<lambda>i. assign (Para n i, e' i))) = (Para n (Suc N), e' (Suc N)) # map (\\<lambda>i. (Para n i, e' i)) (down N)\"
      apply(cut_tac b1 b2,simp)
      done
  qed
qed


lemma valOfLemma[simp]: \"i \\<le> N \\<longrightarrow> (valOf (map (\\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=e i\"
  apply(induct_tac N)
  apply simp
  apply auto
done        

lemma valOfLemma1Aux[simp]: \"i > N \\<longrightarrow> (valOf (map (\\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=  IVar (Para v i)\"
  apply(induct_tac N)
  apply simp
  apply auto
done      


lemma valOfLemma1[simp,intro]: \"i > N \\<Longrightarrow> (valOf (map (\\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=  IVar (Para v i)\"
  by (metis (lifting) valOfLemma1Aux)

lemma valOfLemma2Aux[simp]: \"(var' \\<notin> set (map fst xs)) \\<longrightarrow> (valOf xs (var'))=IVar var'\"
  apply(induct_tac xs)
  apply simp
  apply auto
done  

lemma valOfLemma2[simp,intro]: \"(var' \\<notin> set (map fst xs)) \\<Longrightarrow> (valOf xs (var'))=IVar var'\"
by (metis (lifting) valOfLemma2Aux)
  
lemma valOfLemma3 [simp]:\"(\\<forall> i.  var' \\<noteq> Para v i) \\<Longrightarrow>  (valOf (map (\\<lambda>i. (Para v i, e i)) (down N)) var')=IVar var'\"
apply(rule valOfLemma2)
apply(induction N)
by auto

lemma valOfLemma4Aux :\"v \\<notin> set (map fst   (statement2Assigns S)) \\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v\"
    proof(induct_tac S,auto)qed
    
    

lemma valOfLemma4 [simp,intro]:\"v \\<notin> set (map fst   (statement2Assigns S)) \\<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v\"
by (metis valOfLemma4Aux)

lemma valOfLemma5Aux :\"( valOf (statement2Assigns   S ) v=IVar v) \\<and>    ( valOf (statement2Assigns S') v=IVar v)\\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v=IVar v) \"
    proof(induct_tac S,auto)qed
    
lemma valOfLemma5 [simp,intro]:\"( valOf (statement2Assigns   S ) v=IVar v) \\<and>    ( valOf (statement2Assigns S') v=IVar v)  \\<Longrightarrow> ( valOf (statement2Assigns  (cat S S')) v=IVar v) \"
  by(metis  valOfLemma5Aux)
  
lemma valOfLemma6Aux :\"( valOf (statement2Assigns   S ) v=IVar v) \\<and>    ( valOf (statement2Assigns S') v=IVar v)\\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v=IVar v) \"
    proof(induct_tac S,auto)qed
    
lemma varsOfNot [simp,dest!]:\"v \\<notin> set (map fst   (statement2Assigns S)) \\<Longrightarrow>v \\<in>set( map fst (statement2Assigns  (cat S S'))) = (v \\<in> set (map fst   (statement2Assigns S'))) \"
by (metis Un_iff varsOfSent1 varsOnCat)



(*lemma valOfLemma4 [simp]:\"i\\<noteq>j \\<Longrightarrow>  (valOf (map (\\<lambda>i. (Para v i, e i)) (down N)) var')=IVar var'\"
apply(rule valOfLemma2) 
(statement2Assigns ((parallel ( x', e) S)) )
apply(induction N)
by auto*)  
primrec andList::\"formula list \\<Rightarrow> formula\" where
\"andList [] = chaos\" |
\"andList (frm#frms) = andForm frm (andList frms)\" 

lemma andList2Aux:
   shows \"formEval (neg frm) s \\<longrightarrow> frm \\<in>set frms \\<longrightarrow> formEval (neg (andList frms)) s\"
   proof(induct_tac frms,auto)qed
   
lemma andList2:
   shows \"formEval (neg frm) s \\<Longrightarrow> frm \\<in>set frms \\<Longrightarrow> formEval (neg (andList frms)) s\"
   by (metis andList2Aux)
   
lemma andList1Aux:
   shows \"formEval ( (andList frms)) s  \\<longrightarrow> frm \\<in>set frms \\<longrightarrow> formEval ( frm) s \"
   proof(induct_tac frms,auto)qed
   
lemma andList1:
   shows \"formEval ( (andList frms)) s  \\<Longrightarrow>  frm \\<in>set frms \\<Longrightarrow> formEval ( frm) s \" 
    by (metis andList1Aux)
lemma resAux1:
  assumes   b:\"formEval frm s\" and c:\"formEval (neg (andList (frm#frms))) s\"
  shows\"formEval (neg (andList frms)) s\"
  apply(cut_tac b c)
  apply auto
  done
  
  
lemma noEffectSubstAux:
  
  shows \" (  (varOfExp e \\<inter>  (varOfSent S) ={}) \\<longrightarrow>(substExpByStatement e S)  =e) \\<and>
           (  (varOfForm f \\<inter>  (varOfSent S) ={} )\\<longrightarrow> (substFormByStatement f S)  =  f )\"
           
    (is \"(( ?condOne e S\\<longrightarrow> ?LHS e S=?RHS e S)\\<and> (?condOnf f S\\<longrightarrow> ?LHS1 f S=?RHS1 f S))\")
  proof(induct_tac e and f)
      fix v
      let ?e=\"(IVar v)\"
      show  \"?condOne ?e S\\<longrightarrow>?LHS ?e S=?RHS ?e S\"
      proof(induct_tac S)
        fix prod
        let ?S=\"assign prod\"
        show \"?condOne ?e ?S \\<longrightarrow>?LHS ?e ?S=?RHS ?e ?S\"
        
        apply(unfold  substExpByStatement_def trans_def,auto)
        done
    next
       fix prod S
       let ?S=\"parallel prod S\"
       assume b1:\"?condOne ?e S \\<longrightarrow>?LHS ?e S=?RHS ?e S\"
       
       show \"?condOne ?e ?S \\<longrightarrow> ?LHS ?e ?S=?RHS ?e ?S\"
       
       proof(unfold  substExpByStatement_def trans_def,
       case_tac \"fst prod =v\",force)
       assume d1:\"fst prod \\<noteq> v \"
       show \"varOfExp (IVar v) \\<inter> varOfSent (parallel prod S) = {} \\<longrightarrow> (substExp (IVar v) (statement2Assigns (parallel prod S))) =
               (IVar v)\"
       proof(cut_tac d1,simp,case_tac \"(varOfExp ?e) \\<inter>  set (map fst (statement2Assigns S) )={}\")
        assume e1:\"(varOfExp ?e) \\<inter>  set (map fst (statement2Assigns S) )={}\"
        have f1:\"v \\<notin> fst ` set (statement2Assigns S)\"
        apply(cut_tac e1,simp)
        done
        have f2:\" expEval ?e s  =  expEval ?e (transAux (statement2Assigns S) s)\"
          apply(cut_tac e1)
          by (metis (no_types) noEffectOnExpAux)

        show \" v \\<notin> varOfSent S \\<longrightarrow> valOf (statement2Assigns S) v = IVar v\"
          by (metis valOfLemma2 varsOfSent1)
         
        next
        assume  e1:\"(varOfExp ?e) \\<inter>  set (map fst (statement2Assigns S) )\\<noteq>{}\"
        have f1:\"v \\<in> fst ` set (statement2Assigns S)\"
        apply(cut_tac e1,simp)
        done
      show \" v \\<notin> varOfSent S \\<longrightarrow> valOf (statement2Assigns S) v = IVar v\"
          by (metis valOfLemma2Aux varsOfSent1)
      
      qed 
    qed
  qed
next 
  fix n
  let ?e=\"(Const n)\"
      show  \"?condOne ?e S \\<longrightarrow>?LHS ?e S=?RHS ?e S\"
      apply( simp)
      done
next
  fix f e1 e2
  assume a1:\" (?condOnf f S \\<longrightarrow> ?LHS1 f S=?RHS1 f S)\" and
  a2:\"?condOne e1 S \\<longrightarrow>?LHS e1 S=?RHS e1 S\" and a3:\"?condOne e2 S \\<longrightarrow>?LHS e2 S=?RHS e2 S\"
  let ?e=\"iteForm f e1 e2\"
  show \"?condOne ?e S \\<longrightarrow>?LHS ?e S=?RHS ?e S\"  
  proof(rule impI)
  assume b1:\"?condOne ?e S\"
  have c1:\"?condOnf f S \"
  apply(cut_tac b1,simp)
  by (metis bot_eq_sup_iff inf_sup_distrib2)
  have c2:\"?condOne e1 S \"
   apply(cut_tac b1,simp)
   by (metis c1 inf_bot_right inf_sup_absorb inf_sup_distrib2 sup_bot.left_neutral)
  have c3:\"?condOne e2 S \"
   apply(cut_tac b1,simp)
   by (metis c1 inf_bot_right inf_sup_absorb inf_sup_distrib2 sup_bot.left_neutral)
 with c1 c2 c3 a1 a2 a3
 show \"?LHS ?e S=?RHS ?e S\"
 by (metis substExpByStatement_def substExpite substFormByStatement_def)  
 qed 
 
next
  fix e1 e2
  
  assume a1:\"?condOne e1 S \\<longrightarrow>?LHS e1 S=?RHS e1 S\" and a2:\"?condOne e2 S \\<longrightarrow>?LHS e2 S=?RHS e2 S\"
  let ?f=\"eqn e1 e2\"
  
  show \"(?condOnf ?f S \\<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)\"
  proof(rule impI)
  assume b1:\"?condOnf ?f S\"
  have c1:\"?condOne e1 S\"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 sup_eq_bot_iff)
  have c2:\"?condOne e2 S\"
  apply(cut_tac b1,simp)
   by (metis Int_Un_distrib2 sup_eq_bot_iff)
   with a1 a2 c1 c2 
   show \"?LHS1 ?f S=?RHS1 ?f S\"
    by simp
   qed
next
  fix f1 f2
  assume a1:\" (?condOnf f1 S \\<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)\" and  a2:\" (?condOnf f2 S \\<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)\"
  let ?f=\"andForm f1 f2\"
  
  show \"(?condOnf ?f S \\<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)\"
  proof(rule impI)
  assume b1:\"?condOnf ?f S\"
  have c1:\"?condOnf f1 S\"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:\"?condOnf f2  S\"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show \"?LHS1 ?f S=?RHS1 ?f S\"
   by auto
   qed
next
  fix f1
  assume a1:\" (?condOnf f1 S \\<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)\"
  let ?f=\"neg f1\"
  show \"( ?condOnf ?f S \\<longrightarrow>?LHS1 ?f S=?RHS1 ?f S)\"
  proof(rule impI)
  assume b1:\"?condOnf ?f S\"
  have c1:\"?condOnf f1 S\"
  by(cut_tac b1,simp)
  
   with a1 c1
   show \"?LHS1 ?f S=?RHS1 ?f S\"
   by auto
   qed
 
next   
  fix f1 f2
  assume a1:\" (?condOnf f1 S \\<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)\" and  a2:\" (?condOnf f2 S \\<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)\"
  let ?f=\"implyForm f1 f2\"
  
  show \"(?condOnf ?f S \\<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)\"
  proof(rule impI)
  assume b1:\"?condOnf ?f S\"
  have c1:\"?condOnf f1 S\"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:\"?condOnf f2  S\"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show \"?LHS1 ?f S=?RHS1 ?f S\"
   by auto
   
  qed
  
next
  let ?f=\"chaos\"
  show \"( ?condOnf ?f S \\<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)\"
  by auto
next
  next   
  fix f1 f2
  assume a1:\" (?condOnf f1 S \\<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)\" and  a2:\" (?condOnf f2 S \\<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)\"
  let ?f=\"orForm f1 f2\"
  
  show \"(?condOnf ?f S \\<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)\"
  proof(rule impI)
  assume b1:\"?condOnf ?f S\"
  have c1:\"?condOnf f1 S\"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:\"?condOnf f2  S\"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show \"?LHS1 ?f S=?RHS1 ?f S\"
   by auto
   
  qed
qed

lemma noEffectSubstExp [intro!]:
  
  shows \" (  (varOfExp e \\<inter>  (varOfSent S) ={}) \\<Longrightarrow>(substExpByStatement e S)  =e) \"
by (metis noEffectSubstAux)
  
lemma noEffectSubstForm [intro!]:
  
  shows \" 
             (varOfForm f \\<inter>  (varOfSent S) ={}) \\<Longrightarrow> (substFormByStatement f S)  =  f \"
 by (metis noEffectSubstAux) 
 
 lemma noEffectValOfStatementAux[intro]:
  shows \"( v \\<notin>  (varOfSent S) )\\<longrightarrow> valOf (statement2Assigns  S)  v=IVar v\" (is \"?P N\") 
 proof(induct_tac S,auto)qed
 
  lemma noEffectValOfStatement[simp,intro]:
  assumes \"( v \\<notin>  (varOfSent S)) \"
  shows   \"valOf (statement2Assigns  S)  v=IVar v\" (is \"?P N\")
by (metis assms valOfLemma2Aux varsOfSent1) 
 
 lemma noEffectValOfForallStatementAux[intro]:
  shows \"( \\<forall>i. (v\\<notin>  (varOfSent (ps i)) ))\\<longrightarrow> valOf (statement2Assigns  (forallSent (down N) ps)) v=IVar v\" (is \"?P N\")
  proof(induct_tac N)
    show \"?P 0\"
      apply simp
      done
   next
    fix N
    assume b1:\"?P N\"
    show \"?P (Suc N)\"
    proof(rule impI)
      assume c1:\" \\<forall>i. v \\<notin> varOfSent (ps i)\"
      show \"valOf (statement2Assigns (forallSent (down (Suc N)) ps)) v = IVar v\"
      proof(rule noEffectValOfStatement)
        have \"   varOfSent (forallSent (down (Suc N)) ps) \\<inter>{v} = {}\"  thm forallVars
        proof(rule  forallVars,cut_tac c1,auto)qed
        then show   \" v \\<notin> varOfSent (forallSent (down (Suc N)) ps)\"
        by (metis c1 forallVars1) 
      qed
  qed 
  qed
  
 lemma noEffectValOfForallStatement[simp,intro]:
  shows \"( \\<forall>i. (v \\<notin>  (varOfSent (ps i))) ) \\<Longrightarrow>  valOf (statement2Assigns  (forallSent (down N) ps)) v=IVar v\" 
  by(metis noEffectValOfForallStatementAux)
  
 lemma noEffectValOfForallStatement1[simp,intro]:
  shows \"( \\<forall>i. (v \\<notin>  (varOfSent (ps i))) ) \\<Longrightarrow>  expEval ( valOf (statement2Assigns  (forallSent (down N) ps)) v) s=s  v\"
by auto

lemma valOfLemma7Aux:\"v \\<notin> varOfSent S \\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v\"
proof(induct_tac S,auto)qed

lemma valOfLemma7 [simp,intro]:\"v \\<notin> varOfSent S \\<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v\"
by(metis valOfLemma7Aux)

lemma valOfLemma8Aux:\"v \\<in> varOfSent S \\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S)) v\"
proof(induct_tac S,auto)qed

lemma valOfLemma8A[simp,intro]:\"v \\<in> varOfSent S \\<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S)) v\"
by(metis valOfLemma8Aux)

thm noEffect
lemma  noEffectOnRule[simp,intro]:
  assumes a1:\"  (varOfForm f \\<inter>  (varOfSent (act r)) ={})\"
  shows \" invHoldForRule' s f r R \"  (is \"?P1 s \\<or> ?P2 s \\<or> ?P3 s\")
proof -
  have \"?P2 s\"
  using assms noEffectSubstForm by auto
  then show \"?P1 s \\<or> ?P2 s \\<or> ?P3 s\"
  by auto
qed
end
"

