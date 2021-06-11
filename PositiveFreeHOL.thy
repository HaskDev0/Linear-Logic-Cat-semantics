theory PositiveFreeHOL
  imports Main 

begin

nitpick_params [sat_solver = MiniSat_JNI, max_threads = 1,debug=true]
declare [[smt_timeout = 400]]


typedecl i \<comment> \<open>The base type for individuals\<close>
consts fExistence :: "'a \<Rightarrow> bool" ("E") 

consts fStar :: "i" ("\<star>")

consts fUndef :: "'a" ("\<^bold>e")
axiomatization where fUndefIAxiom: "\<not>E (\<^bold>e::i)" 
axiomatization where fFalsehoodBAxiom: "(\<^bold>e::bool) = False" 
axiomatization where fTrueAxiom: "E True"
axiomatization where fFalseAxiom: "E False"

abbreviation fNot :: "bool\<Rightarrow>bool" ("\<^bold>\<not>")
  where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"
abbreviation fImplies (infixr "\<^bold>\<rightarrow>" 13)       
 where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
abbreviation fIdentity (infixr "\<^bold>=" 13)       
 where "l \<^bold>= r \<equiv> l = r"
abbreviation fForall ("\<^bold>\<forall>")              
 where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E x \<longrightarrow> \<Phi> x"   
abbreviation fForallBinder (binder "\<^bold>\<forall>" [8] 9)
 where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"
abbreviation fThat:: "('a\<Rightarrow>bool)\<Rightarrow>'a" ("\<^bold>I") 
 where "\<^bold>I\<Phi> \<equiv> if \<exists>x. E(x) \<and> \<Phi>(x) \<and> (\<forall>y. (E(y) \<and> \<Phi>(y)) \<longrightarrow> (y = x)) 
              then THE x. E(x) \<and> \<Phi>(x)
              else \<^bold>e"

abbreviation fThatBinder:: "('a\<Rightarrow>bool)\<Rightarrow>'a"  (binder "\<^bold>I" [8] 9) 
  where "\<^bold>Ix. \<phi>(x) \<equiv> \<^bold>I(\<phi>)"

abbreviation fSome :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" ("\<^bold>SOME") \<comment> \<open>Here we added the corresponding definition in Free Logic for indefinite description SOME operator, but as for this work, everywhere it could be replaced by the ordinary one\<close>
  where "\<^bold>SOME\<Phi> \<equiv> if \<exists>x. E(x) \<and> \<Phi>(x)
                  then SOME x. E(x) \<and> \<Phi>(x)
                  else \<^bold>e"

abbreviation fSomeBinder:: "('a \<Rightarrow> bool) \<Rightarrow> 'a" (binder "\<^bold>SOME" [8]9)
  where "\<^bold>SOMEx. \<phi>(x) \<equiv> \<^bold>SOME(\<phi>)" 

abbreviation fOr (infixr "\<^bold>\<or>" 11)                                 
 where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 12)                                
 where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"    
abbreviation fImplied (infixr "\<^bold>\<leftarrow>" 13)       
 where "\<phi> \<^bold>\<leftarrow> \<psi> \<equiv> \<psi> \<^bold>\<rightarrow> \<phi>" 
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 15)                             
 where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)"  
abbreviation fExists ("\<^bold>\<exists>")                                       
 where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     
  where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"

abbreviation fEx1 :: "('a \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<exists>!") \<comment> \<open>The same as for fSome operator: unique existence operator for Free Logic, that indeed again could be replaced by the ordinary one\<close>
  where "fEx1 P \<equiv> \<^bold>\<exists>x. (P x \<and> (\<^bold>\<forall>y. P y \<longrightarrow> y = x))"

abbreviation fEx1Binder (binder "\<^bold>\<exists>!" [8]9) 
  where "\<^bold>\<exists>!x. \<phi> x \<equiv> \<^bold>\<exists>!\<phi>" 

end