theory Symmetric_Closed_Monoidal_Category
  imports Closed_Monoidal_Category

begin

section \<open>Symmetric closed monoidal category\<close>

locale SymmetricMonClosedCat = 
LM: LeftClosedMonCatBifunctor domain codomain composition nonex T \<alpha> \<mu> \<rho> \<e> Impl \<Phi> \<Psi> +
Sym: Symmetry domain codomain composition nonex T \<alpha> \<gamma> 
for
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  T :: "'a * 'a \<Rightarrow> 'a" and 
  \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a" and
  \<mu> :: "'a \<Rightarrow> 'a" and 
  \<rho> :: "'a \<Rightarrow> 'a" and
  \<e> :: "'a" and 
  \<gamma> :: "'a * 'a \<Rightarrow> 'a" and 
  Impl :: "'a * 'a \<Rightarrow> 'a" and
  \<Phi> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and
  \<Psi> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" + 
fixes 
  FalseM :: "'a" ("\<bottom>\<^sub>m") 
assumes 
  FM: "LM.A.IdEx (\<bottom>\<^sub>m)" 
begin

subsection \<open>Definition of right closed structure via left closed structure\<close>

abbreviation Impr
  where "Impr AB \<equiv> Impl AB" 

abbreviation ImprA (infix "\<circ>-" 56)
  where "y \<circ>- x \<equiv> Impr(y,x)" 

abbreviation \<Phi>r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  where "\<Phi>r b a x \<equiv> \<Phi> a b (x\<cdot>\<gamma>(a,b))" 

abbreviation \<Psi>r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  where "\<Psi>r a c x \<equiv> (\<Psi> a c x)\<cdot>\<gamma>(dom x,a)"

lemma \<Phi>r_simp[simp]: 
  assumes "LM.A.Id a \<and> LM.A.Id b" 
  shows "\<Phi>r b a x = \<Phi> a b (x\<cdot>\<gamma>(a,b))" by blast

lemma RCS_A1: 
  assumes "LM.A.Id a \<and> LM.A.Id b" and "E f" 
  shows "T(b,f)\<cdot>\<gamma>(dom f,b) \<cong> \<gamma>(cod f,b)\<cdot>T(f,b)" 
  by (smt LM.A.Ex_two_ob2 LM.A.Id3 LM.A.S5 LM.A.S6 LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp Sym.Braid.Br.\<eta>.naturality Sym.Braid.Br.\<eta>.nntExists Sym.Braid.Br.\<eta>.preserves_comp assms(1) assms(2) fst_conv snd_conv)

lemma RCS_B1: 
  assumes "LM.A.Id a \<and> LM.A.Id b" and "E f" 
  shows "T(f,a)\<cdot>\<gamma>(a,dom f) \<cong> \<gamma>(a,cod f)\<cdot>T(a,f)" 
  using Sym.Braid.Br.\<eta>.naturality by (smt LM.A.Ex_two_ob1 LM.A.Id3 LM.Impl.AopxA.prod_S5 LM.M.AxA.Ex LM.M.T.BiF.reflects_morp Sym.Braid.Br.\<eta>.nntExists Sym.Braid.Br.\<eta>.preserves_comp assms(1) assms(2) fst_conv snd_conv)

lemma RCS_A: 
  assumes "(f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (LM.A.IdEx a) \<and> (LM.A.IdEx b) \<and> ((cod x) = a)"
  shows "(\<Phi>r b (dom x) (f \<cdot> (b\<otimes>x)) \<simeq> (x\<circ>-c)\<cdot>(\<Phi>r b a f))"
proof-
  have 01: "E x" using LM.A.S2 assms by blast
  have 1: "LM.A.from_hom_seta (f\<cdot>\<gamma>(a,b)) (T(a,b)) c" by (smt LM.A.Id2 LM.A.Id_ex LM.A.S3 LM.A.S5 LM.A.cod_of_comp LM.A.dom_of_comp LM.M.tensor_ide Sym.Braid.Br.\<eta>.presCod Sym.Braid.Br.\<eta>.presDom assms fst_conv snd_conv)
  then have 2: "(x-\<circ>c)\<cdot>(\<Phi> a b (f\<cdot>\<gamma>(a,b))) \<simeq> (\<Phi> (dom x) b ((f\<cdot>\<gamma>(a,b))\<cdot>T(x,b)))" using LM.NaturalityA by (metis assms)
  also have 3: "(\<Phi>r b (dom x) (f \<cdot> (T(b,x))) = (\<Phi> (dom x) b ((f\<cdot>T(b,x))\<cdot>\<gamma>((dom x),b))))" by blast
  have 4: "(\<Phi> (dom x) b ((f\<cdot>T(b,x))\<cdot>\<gamma>((dom x),b))) = (\<Phi> (dom x) b (f\<cdot>(T(b,x)\<cdot>\<gamma>((dom x),b))))" by (smt "01" LM.A.Ex_from_hom_set LM.A.FHS LM.A.Id2 LM.A.Id3 LM.A.Id_ex2 LM.A.S3 LM.A.dom_of_comp LM.A.from_hom_set_def LM.Aop.S3 LM.Aop.S4 LM.Aop.S6 LM.Aop.dom_cod LM.M.T.BiF.pres1 LM.M.T.BiF.pres2 LM.M.T.BiF.reflects_morp LM.M.tensor_arrow_2 LM.M.tensor_codomain LM.M.tensor_domain Sym.Braid.Br.G.ntExists Sym.Braid.Br.\<eta>.ntExists Sym.Braid.Br_inv.presCod Sym.symmetry assms fst_eqD snd_eqD)
  have 5: "T(b,x)\<cdot>\<gamma>((dom x),b) = (\<gamma>(a,b)\<cdot>T(x,b))" by (smt "01" LM.A.Ex_two_ob2 LM.A.S5 LM.A.S6 LM.M.T.BiF.reflects_morp LM.M.tensor_arrow_2 Sym.Braid.Br.\<eta>.naturality Sym.Braid.Br.\<eta>.preserves_comp assms fst_conv snd_conv)
  then have 6: "(\<Phi> (dom x) b (f\<cdot>(T(b,x)\<cdot>\<gamma>((dom x),b)))) = (\<Phi> (dom x) b (f\<cdot>(\<gamma>(a,b)\<cdot>T(x,b))))" by presburger
  then have 7: "(\<Phi>r b (dom x) (f \<cdot> (T(b,x))) \<simeq> (x\<circ>-c)\<cdot>(\<Phi>r b a f))" by (metis "1" "4" LM.A.S1 LM.A.S4 LM.Aop.ExDomCod(1) LM.M.tensor_morph assms calculation)
  then show ?thesis by blast
qed

lemma RCS_B: 
  assumes "(f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (LM.A.IdEx a) \<and> (LM.A.IdEx b) \<and> ((cod y) = b)"
  shows "(\<Phi>r (dom y) a (f \<cdot> (y\<otimes>a)) \<simeq> (\<Phi>r b a f)\<cdot>y)" 
proof-
  have 01: "E f" using LM.A.par_ex2 assms by blast
  have 1: "LM.A.from_hom_seta (f\<cdot>\<gamma>(a,b)) (T(a,b)) c" by (smt LM.A.Id_ex LM.A.Id_ex2 LM.A.S3 LM.A.cod_of_comp LM.A.dom_of_comp LM.Aop.dom_cod LM.M.tensor_arrow_2 LM.M.tensor_ide Sym.Braid.Br.\<eta>.presCod Sym.Braid.Br.\<eta>.presDom assms fst_conv snd_conv)
  then have 2: "((\<Phi> a (dom y) ((f\<cdot>\<gamma>(a,b)) \<cdot> (T(a,y))) \<simeq> (\<Phi> a b (f\<cdot>\<gamma>(a,b)))\<cdot>y))" using LM.NaturalityB using assms by blast
  also have 3: "(\<Phi>r (dom y) a (f \<cdot> (T(y,a))) = (\<Phi> a (dom y) ((f\<cdot>T(y,a))\<cdot>\<gamma>(a,(dom y)))))" by blast
  have 4: "(\<Phi> a (dom y) ((f\<cdot>T(y,a))\<cdot>\<gamma>(a,(dom y)))) = (\<Phi> a (dom y) (f\<cdot>(T(y,a)\<cdot>\<gamma>(a,(dom y)))))" by (smt LM.A.Ex_two_ob2 LM.A.S1 LM.A.S3 LM.A.S4 LM.A.S5 LM.M.AxA.Ex2 Sym.Braid.Br.\<eta>.naturality assms calculation fst_conv snd_conv)
  have 5: "T(y,a)\<cdot>\<gamma>(a,(dom y)) = \<gamma>(a,cod y)\<cdot>T(a,y)" by (smt LM.A.Id_ex2 LM.Aop.Ex_two_ob1 LM.Aop.S6 LM.M.AxA.Ex RCS_B1 Sym.Braid.Br.\<eta>.naturality assms calculation fst_conv snd_conv)
  then have 6: "(\<Phi> a (dom y) (f\<cdot>(T(y,a)\<cdot>\<gamma>(a,(dom y))))) = (\<Phi> a (dom y) (f\<cdot>(\<gamma>(a,cod y)\<cdot>T(a,y))))" by presburger
  then have 7: "((\<Phi>r (dom y) a (f \<cdot> (T(y,a))) \<simeq> (\<Phi>r b a f)\<cdot>y))" by (smt LM.A.S1 LM.A.S3 LM.A.S4 LM.A.S5 LM.A.S6 LM.M.T.BiF.reflects_morp LM.M.tensor_arrow_2 Sym.Braid.Br.\<eta>.naturality assms calculation fst_conv snd_conv)
  then show ?thesis by blast
qed

lemma RCS_C: 
  assumes "(f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (LM.A.IdEx a) \<and> (LM.A.IdEx b) \<and> ((dom z) = c)"
  shows "(\<Phi>r b a (z \<cdot> f) \<simeq> ((a\<circ>-z))\<cdot>(\<Phi>r b a f))"
proof-
  have 01: "E f" using assms LM.A.S1 by blast
  have 1: "LM.A.from_hom_seta (f\<cdot>\<gamma>(a,b)) (T(a,b)) c" by (smt LM.A.Id_ex LM.A.Id_ex2 LM.A.S3 LM.A.cod_of_comp LM.A.dom_of_comp LM.Aop.dom_cod LM.M.tensor_arrow_2 LM.M.tensor_ide Sym.Braid.Br.\<eta>.presCod Sym.Braid.Br.\<eta>.presDom assms fst_conv snd_conv)
  then have 2: "(\<Phi> a b (z \<cdot> (f\<cdot>\<gamma>(a,b))) \<simeq> (a-\<circ>z)\<cdot>(\<Phi> a b (f\<cdot>\<gamma>(a,b))))" using LM.NaturalityC using assms by blast
  also have 3: "\<Phi>r b a (z \<cdot> f) = (\<Phi> a b ((z \<cdot> f) \<cdot>\<gamma>(a,b)))" by blast 
  then have 4: "((\<Phi>r b a (z \<cdot> f) \<simeq> (a\<circ>-z)\<cdot>\<Phi>r b a f))" by (metis "1" LM.A.S3 LM.A.S4 assms calculation)
  then show ?thesis by blast
qed

lemma RCS_ABC: 
  assumes "((f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (LM.A.IdEx a) \<and> (LM.A.IdEx b) \<and> ((cod x) = a) \<and> ((cod y) = b) \<and> ((dom z) = c))" 
  shows "(\<Phi>r (dom y) (dom x) (z\<cdot>(f\<cdot>(y\<otimes>x))) \<simeq> (Impr(x,z))\<cdot>((\<Phi>r b a f)\<cdot>y))"
proof-
  have 1: "(((f\<cdot>\<gamma>(a,b)):(a\<otimes>b)\<rightarrow>\<^sub>Ac) \<and> (LM.A.IdEx a) \<and> (LM.A.IdEx b) \<and> ((cod x) = a) \<and> ((cod y) = b) \<and> ((dom z) = c))" by (smt LM.A.Id_ex LM.A.Id_ex2 LM.A.S3 LM.A.cod_of_comp LM.A.dom_of_comp LM.Aop.dom_cod LM.M.tensor_arrow_2 LM.M.tensor_ide Sym.Braid.Br.\<eta>.presCod Sym.Braid.Br.\<eta>.presDom assms fst_conv snd_conv)
  then have 2: "(\<Phi> (dom x) (dom y) (z\<cdot>((f\<cdot>\<gamma>(a,b))\<cdot>(x\<otimes>y)))) \<simeq> (Impl(x,z))\<cdot>((\<Phi> a b (f\<cdot>\<gamma>(a,b)))\<cdot>y)" using LM.NaturalityD\<Phi> by blast
  have 3: "(z\<cdot>((f\<cdot>\<gamma>(a,b))\<cdot>(x\<otimes>y))) \<simeq> (z\<cdot>(f\<cdot>(\<gamma>(a,b)\<cdot>(x\<otimes>y))))" by (smt "1" LM.A.FHS LM.A.S2 LM.A.S3 LM.A.S4 LM.Aop.ExDomCod(1) LM.M.tensor_codomain)
  have 4: "\<gamma>(cod x,cod y)\<cdot>(x\<otimes>y) \<cong> (y\<otimes>x)\<cdot>\<gamma>(dom x, dom y)" using Sym.Braid.Br.\<eta>.naturality by (smt LM.A.Ex_two_ob1 LM.A.Ex_two_ob2 LM.A.FHS LM.A.S6 LM.A.cod_of_comp LM.M.AxA.Ex2 LM.M.T.BiF.nntExists LM.M.tensor_codomain Sym.Braid.Br.\<eta>.ActOnMorph fst_eqD snd_eqD)
  then show ?thesis using 2 3 by (metis "1" LM.A.Ex_two_ob2 LM.A.S4)
qed
       
interpretation RightClosedStr: RightClosedMonCatBifunctor domain codomain composition nonex T \<alpha> \<mu> \<rho> \<e> Impr \<Phi>r \<Psi>r
  apply unfold_locales
  apply (smt LM.A.Id_ex LM.A.S3 LM.A.cod_of_comp LM.A.dom_of_comp LM.Aop.dom_cod LM.FunctionSet\<Phi> LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp LM.M.tensor_arrow_2 LM.M.tensor_ide Sym.Braid.Br.\<eta>.presCod Sym.Braid.Br.\<eta>.presDom fst_conv snd_conv)
  apply (smt LM.A.Id_ex LM.A.Id_ex2 LM.A.S3 LM.A.S5 LM.A.cod_of_comp LM.A.dom_of_comp LM.Aop.double_cod LM.FunctionSet\<Psi> LM.Impl.BiF.nntExists LM.M.AxA.Ex2 LM.M.tensor_ide Sym.Braid.Br.\<eta>.presCod Sym.Braid.Br.\<eta>.presDom fst_conv snd_conv)
  apply (smt LM.A.Id_ex LM.A.Id_ex2 LM.A.S3 LM.A.S4 LM.A.S5 LM.A.arrow_and_inv1 LM.A.cod_of_comp LM.BijectionOne LM.FunctionSet\<Phi> LM.M.AxA.Ex2 LM.M.tensor_ide Sym.Braid.Br.\<eta>.ntExists Sym.Braid.Br_inv.comp_iso Sym.Braid.Br_inv.identity_under_map Sym.Braid.Br_inv.int1 Sym.symmetry fst_conv snd_conv)
  apply (smt LM.A.Id_ex2 LM.A.S3 LM.A.S4 LM.A.S5 LM.A.arrow_and_inv1 LM.A.from_hom_set_def LM.Aop.double_cod LM.BijectionTwo LM.FunctionSet\<Psi> LM.M.AxA.Ex2 Sym.Braid.Br.comp_iso Sym.Braid.Br_inv.identity_under_map Sym.Braid.Br_inv.int1 Sym.symmetry fst_conv snd_conv)
  using RCS_ABC by blast

theorem RightMonoidalStructure: 
  shows "RightClosedMonCatBifunctor domain codomain composition nonex T \<alpha> \<mu> \<rho> \<e> Impr \<Phi>r \<Psi>r" 
  using RightClosedStr.RightClosedMonCatBifunctor_axioms by blast

subsection \<open>Naturality of inverse bijection\<close>

lemma NaturalityInvA: 
  assumes "((x:b\<rightarrow>\<^sub>A(a-\<circ>c)) \<and> LM.A.Id a \<and> LM.A.Id c) \<and> ((cod f) = a)"
  shows "((\<Psi> a c x)\<cdot>T(f,b)) \<simeq> (\<Psi> (dom f) c ((f-\<circ>c)\<cdot>x))" 
proof
  assume n:  "\<^bold>\<not> (E ((f \<otimes> b) \<cdot>op \<Psi> a c x)) \<^bold>\<or>
    \<^bold>\<not> (\<^bold>\<not> (\<^bold>\<not> (E (\<Psi> (LM.Aop.codop f) c (x \<cdot>op RightClosedStr.RImplication f c))) \<^bold>\<or>
             (f \<otimes> b) \<cdot>op \<Psi> a c x \<noteq>
             \<Psi> (LM.Aop.codop f) c (x \<cdot>op RightClosedStr.RImplication f c)))"
  hence n2: "\<not>((\<Psi> a c x)\<cdot>T(f,b) \<simeq> \<Psi> (dom f) c ((f-\<circ>c)\<cdot>x))" by blast 
  have 1: "\<not>((\<Psi> a c x)\<cdot>T(f,b) \<simeq> \<Psi> (dom f) c ((f-\<circ>c)\<cdot>(\<Phi> a b (\<Psi> a c x))))" by (metis LM.A.Id_ex LM.BijectionTwo LM.Impl.BiF.nntExists LM.M.AxA.Ex assms n)
  hence 2: "\<not>(\<Phi> (dom f) b ((\<Psi> a c x)\<cdot>T(f,b)) \<simeq> \<Phi> (dom f) b (\<Psi> (dom f) c ((f-\<circ>c)\<cdot>(\<Phi> a b (\<Psi> a c x)))))" by (smt LM.A.Ex_two_ob2 LM.A.Id_ex LM.A.S2 LM.A.S5 LM.Aop.double_cod LM.BijectionOne LM.FunctionSet\<Psi> LM.Impl.BiF.nntExists LM.M.AxA.Ex2 LM.M.tensor_morph LM.NaturalityA assms)
  also have 3: "\<Phi> (dom f) b ((\<Psi> a c x)\<cdot>T(f,b)) \<simeq> ((f-\<circ>c)\<cdot>(\<Phi> a b (\<Psi> a c x)))" by (smt LM.A.Id_ex LM.Aop.double_cod LM.FunctionSet\<Psi> LM.Impl.BiF.nntExists LM.M.AxA.Ex2 LM.NaturalityA assms)
  show False using 2 3 LM.FunctionSet\<Psi> LM.BijectionOne by (smt LM.A.Id_ex LM.A.S3 LM.A.S5 LM.A.dom_of_comp LM.BijectionTwo LM.Impl.BiF.nntExists LM.Impl_morph LM.M.AxA.Ex2 assms)
qed

lemma NaturalityInvB: 
  assumes "(x:b\<rightarrow>\<^sub>A(a-\<circ>c)) \<and> LM.A.Id a \<and> LM.A.Id c \<and> ((cod f) = b)"
  shows "(\<Psi> a c x)\<cdot>T(a,f) \<simeq> \<Psi> a c (x\<cdot>f)" 
proof
  assume n: "\<^bold>\<not> (E (T (a, f) \<cdot>op \<Psi> a c x)) \<^bold>\<or>
    \<^bold>\<not> (\<^bold>\<not> (\<^bold>\<not> (E (\<Psi> a c (f \<cdot>op x))) \<^bold>\<or> T (a, f) \<cdot>op \<Psi> a c x \<noteq> \<Psi> a c (f \<cdot>op x)))"
  then have n2: "\<not>((\<Psi> a c x)\<cdot>T(a,f) \<simeq> \<Psi> a c (x\<cdot>f))" by blast
  have 1: "\<not>((\<Psi> a c x)\<cdot>T(a,f) \<simeq> \<Psi> a c ((\<Phi> a b (\<Psi> a c x))\<cdot>f))" by (metis LM.A.Id_ex LM.BijectionTwo LM.Impl.BiF.reflects_morp LM.M.AxA.Ex assms n)
  hence 2: "\<not>(\<Phi> a (dom f) ((\<Psi> a c x)\<cdot>T(a,f)) \<simeq> \<Phi> a (dom f) (\<Psi> a c ((\<Phi> a b (\<Psi> a c x))\<cdot>f)))" by (smt LM.A.FHS LM.A.Id_ex LM.A.S3 LM.A.S5 LM.A.cod_of_comp LM.A.dom_of_comp LM.BijectionOne LM.BijectionTwo LM.FunctionSet\<Psi> LM.Impl.BiF.nntExists LM.M.AxA.Ex2 LM.M.tensor_codomain LM.M.tensor_domain assms)
  also have 3: "\<Phi> a (dom f) ((\<Psi> a c x)\<cdot>T(a,f)) \<simeq> (\<Phi> a b (\<Psi> a c x))\<cdot>f" by (metis LM.A.Id_ex LM.Aop.double_cod LM.FunctionSet\<Psi> LM.Impl.BiF.nntExists LM.M.AxA.Ex2 LM.NaturalityB assms)
  thus False by (smt LM.A.Ex_two_ob2 LM.A.Id_ex LM.A.S5 LM.A.cod_of_comp LM.A.dom_of_comp LM.BijectionTwo LM.Impl.BiF.nntExists LM.M.AxA.Ex2 assms calculation)
qed

lemma NaturalityInvC: 
  assumes "((x:b\<rightarrow>\<^sub>A(Impl(a,c))) \<and> LM.A.Id a \<and> LM.A.Id c) \<and> ((dom f) = c)" 
  shows "(f\<cdot>(\<Psi> a c x)) \<simeq> (\<Psi> a (cod f) ((a-\<circ>f)\<cdot>x))"
proof
  assume n:  "\<^bold>\<not> (E (\<Psi> a c x \<cdot>op f)) \<^bold>\<or>
    \<^bold>\<not> (\<^bold>\<not> (\<^bold>\<not> (E (\<Psi> a (LM.Aop.domop f) (x \<cdot>op RightClosedStr.RImplication a f))) \<^bold>\<or>
             \<Psi> a c x \<cdot>op f \<noteq> \<Psi> a (LM.Aop.domop f) (x \<cdot>op RightClosedStr.RImplication a f)))"
  hence n2: "\<not>((f\<cdot>(\<Psi> a c x)) \<simeq> (\<Psi> a (cod f) (Impl(a,f)\<cdot>x)))" by blast
  hence 1: "\<not>(\<Phi> a b (f\<cdot>(\<Psi> a c x)) \<simeq> \<Phi> a b (\<Psi> a (cod f) (Impl(a,f)\<cdot>x)))" by (smt LM.A.Id_ex LM.A.S3 LM.A.S6 LM.A.cod_of_comp LM.A.dom_of_comp LM.Aop.double_cod LM.BijectionOne LM.BijectionTwo LM.FunctionSet\<Psi> LM.Impl.BiF.nntExists LM.M.AxA.Ex2 LM.NaturalityC assms) 
  also have 2: "\<Phi> a b (f\<cdot>(\<Psi> a c x)) \<simeq> \<Phi> a b (\<Psi> a (cod f) (Impl(a,f)\<cdot>x))" by (smt LM.A.Ex_from_hom_set LM.A.Id_ex LM.A.S3 LM.A.cod_of_comp LM.A.dom_of_comp LM.A.from_hom_set_def LM.Aop.double_cod LM.BijectionOne LM.BijectionTwo LM.FunctionSet\<Psi> LM.Impl.BiF.nntExists LM.M.AxA.Ex2 LM.NaturalityC assms)
  thus False using calculation by blast 
qed

subsection \<open>Double negation\<close>

lemma Delta1: 
  assumes "f:a\<rightarrow>\<^sub>Aa'" 
  shows "((f-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m)\<cdot>(\<Phi>r a (a-\<circ>\<bottom>\<^sub>m) (\<Psi> a \<bottom>\<^sub>m (a-\<circ>\<bottom>\<^sub>m))) 
       = (\<Phi>r a' (a'-\<circ>\<bottom>\<^sub>m) (\<Psi> a' \<bottom>\<^sub>m (a'-\<circ>\<bottom>\<^sub>m)))\<cdot>f"
proof-
  have 1: "LM.A.from_hom_seta ((\<Phi>r a' (a'-\<circ>\<bottom>\<^sub>m) (\<Psi> a' \<bottom>\<^sub>m (a'-\<circ>\<bottom>\<^sub>m)))\<cdot>f) a ((a'-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m)" 
    by (smt FM LM.A.Id_ex2 LM.A.cod_of_comp LM.A.dom_of_comp LM.Aop.Id20 LM.Aop.cod_dom LM.FunctionSet\<Phi> LM.FunctionSet\<Psi> LM.Impl.BiF.ntExists LM.Impl_dom LM.M.AxA.Ex2 RCS_B RightClosedStr.FunctionSet\<Psi> assms fst_conv snd_conv)
  have 2: "((((f-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m)\<cdot>(\<Phi>r a (a-\<circ>\<bottom>\<^sub>m) (\<Psi> a \<bottom>\<^sub>m (a-\<circ>\<bottom>\<^sub>m)))):a\<rightarrow>\<^sub>A((a'-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m))" 
    by (smt "1" FM LM.A.Ex_two_ob1 LM.A.Id2 LM.A.S1 LM.A.S2 LM.A.S5 LM.A.S6 LM.Aop.dom_cod LM.Aop.double_cod LM.FunctionSet\<Psi> LM.Impl.BiF.ntExists LM.Impl_dom LM.Impl_morph LM.M.AxA.Ex2 RightClosedStr.FunctionSet\<Phi> Sym.Braid.Br.\<eta>.ntExists Sym.Braid.Br.\<eta>.presCod assms fst_conv snd_conv)
  have 3: "\<Psi> a \<bottom>\<^sub>m (f-\<circ>\<bottom>\<^sub>m) \<simeq> (\<Psi> a' \<bottom>\<^sub>m (a'-\<circ>\<bottom>\<^sub>m))\<cdot>(f\<otimes>(a'-\<circ>\<bottom>\<^sub>m))" 
    using NaturalityInvA[where ?x = \<open>(a'-\<circ>\<bottom>\<^sub>m)\<close> and ?b = \<open>(a'-\<circ>\<bottom>\<^sub>m)\<close> and ?a = \<open>a'\<close> and ?c = \<open>\<bottom>\<^sub>m\<close> and ?f = \<open>f\<close>] 
    by (smt FM LM.A.Id_def LM.A.S3 LM.Aop.S2 LM.Aop.S5 LM.Aop.S6 LM.Impl.BiF.ntExists LM.LeftClosedMonCatBifunctor_axioms LM.M.AxA.Ex2 LeftClosedMonCatBifunctor.Impl_dom assms)
  have 4: "(\<Psi> a \<bottom>\<^sub>m (a-\<circ>\<bottom>\<^sub>m))\<cdot>(a\<otimes>(f-\<circ>\<bottom>\<^sub>m)) \<simeq> \<Psi> a \<bottom>\<^sub>m (f-\<circ>\<bottom>\<^sub>m)" 
    using NaturalityInvB[where ?x = \<open>(a-\<circ>\<bottom>\<^sub>m)\<close> and ?b = \<open>(a-\<circ>\<bottom>\<^sub>m)\<close> and ?c = \<open>\<bottom>\<^sub>m\<close> and ?a = \<open>a\<close> and ?f = \<open>(a'-\<circ>\<bottom>\<^sub>m)\<close>] 
    by (smt "2" FM LM.A.Id2 LM.A.S2 LM.A.cod_of_comp LM.Aop.S5 LM.Aop.S6 LM.Aop.dom_cod LM.Impl.BiF.nntExists LM.Impl_dom LM.Impl_morph LM.M.AxA.Ex2 NaturalityInvB assms)
  have 5: "LM.A.from_hom_seta (\<Psi> a' \<bottom>\<^sub>m (a'-\<circ>\<bottom>\<^sub>m)) (T(a',(a'-\<circ>\<bottom>\<^sub>m))) \<bottom>\<^sub>m" 
    by (smt FM LM.Aop.Id20 LM.Aop.cod_dom LM.FunctionSet\<Psi> LM.Impl.BiF.ntExists LM.Impl_dom LM.M.AxA.Ex2 assms)
  have 6: "LM.A.from_hom_seta (\<Psi> a \<bottom>\<^sub>m ((a-\<circ>\<bottom>\<^sub>m))) (T(a,(a-\<circ>\<bottom>\<^sub>m))) \<bottom>\<^sub>m" 
    by (smt "1" FM LM.Aop.Id20 LM.Aop.double_cod LM.FunctionSet\<Psi> LM.Impl.BiF.ntExists LM.Impl_dom LM.M.AxA.Ex2)
  obtain a1 where pa1: "a1 = (\<Psi> a' \<bottom>\<^sub>m ((a'-\<circ>\<bottom>\<^sub>m)))" by blast
  obtain a2 where pa2: "a2 = (\<Psi> a \<bottom>\<^sub>m ((a-\<circ>\<bottom>\<^sub>m)))" by blast
  have 7: "(\<Phi>r a' ((a'-\<circ>\<bottom>\<^sub>m)) a1)\<cdot>f \<simeq> \<Phi>r a ((a'-\<circ>\<bottom>\<^sub>m)) (a1\<cdot>T(f,(a'-\<circ>\<bottom>\<^sub>m)))" 
    by (smt "5" LM.Aop.cod_dom LM.Aop.double_dom LM.Impl.BiF.ntExists LM.Impl_dom LM.M.AxA.Ex2 RCS_B assms pa1)
  have 8: "(((f-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m))\<cdot>(\<Phi>r a ((a-\<circ>\<bottom>\<^sub>m)) a2) \<simeq> \<Phi>r a ((a'-\<circ>\<bottom>\<^sub>m)) (a2\<cdot>T(a,(f-\<circ>\<bottom>\<^sub>m)))" 
    by (smt "6" FM LM.A.S1 LM.Aop.dom_cod LM.Aop.double_cod LM.Impl.BiF.ntExists LM.Impl.BiF.pres2 LM.Impl_dom LM.M.AxA.Ex2 RCS_A assms fst_conv pa2 snd_conv) 
  have 9: "(\<Phi>r a' ((a'-\<circ>\<bottom>\<^sub>m)) (\<Psi> a' \<bottom>\<^sub>m ((a'-\<circ>\<bottom>\<^sub>m))))\<cdot>f \<simeq> 
           (\<Phi>r a ((a'-\<circ>\<bottom>\<^sub>m)) (\<Psi> a \<bottom>\<^sub>m ((f-\<circ>\<bottom>\<^sub>m))))" by (metis "3" "7" pa1)
  have 10: "(((f-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m))\<cdot>(\<Phi>r a ((a-\<circ>\<bottom>\<^sub>m)) (\<Psi> a \<bottom>\<^sub>m ((a-\<circ>\<bottom>\<^sub>m)))) \<simeq> 
           (\<Phi>r a ((a'-\<circ>\<bottom>\<^sub>m)) (\<Psi> a \<bottom>\<^sub>m ((f-\<circ>\<bottom>\<^sub>m))))" by (metis "4" "8" pa2)
  show ?thesis using "10" "9" by presburger
qed

abbreviation \<delta> :: "'a \<Rightarrow> 'a" 
  where "\<delta> a \<equiv>  \<Phi>r a (a-\<circ>\<bottom>\<^sub>m) (\<Psi> a \<bottom>\<^sub>m (a-\<circ>\<bottom>\<^sub>m))"

lemma Delta20:
  assumes "LM.A.from_hom_seta f a a'"
  shows "LM.A.commSquareEx (((f-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m)) (\<delta> a) f (\<delta> a')"
proof-
  have 1: "LM.A.IdEx a" by (metis LM.Aop.double_cod assms)
  have 2: "LM.A.IdEx a'" by (metis LM.Aop.cod_dom assms)
  then have 3: "\<delta> a' = \<Phi>r a' ((a'-\<circ>\<bottom>\<^sub>m)) (\<Psi> a' \<bottom>\<^sub>m ((a'-\<circ>\<bottom>\<^sub>m)))" by presburger
  also have 4: "\<delta> a = \<Phi>r a ((a-\<circ>\<bottom>\<^sub>m)) (\<Psi> a \<bottom>\<^sub>m ((a-\<circ>\<bottom>\<^sub>m)))" using 1 by presburger
  then have 5: "E((((f-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m))\<cdot>(\<delta> a))" 
    by (smt "1" FM LM.A.Id_ex2 LM.A.S1 LM.A.S3 LM.Aop.Id20 LM.FunctionSet\<Phi> LM.Impl.BiF.ntExists LM.Impl.BiF.pres2 LM.Impl_dom LM.M.AxA.Ex2 RightClosedStr.FunctionSet\<Psi> assms fst_conv snd_conv)
  have 6: "E((\<delta> a')\<cdot>f)" using 3 1 by (smt "5" Delta1 assms) 
  show ?thesis using Delta1 1 2 3 4 5 6 by (smt assms)
qed

lemma Delta3: 
  assumes "LM.A.IdEx a" 
  shows "(\<delta> a):a\<rightarrow>\<^sub>A((a-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m)" 
  by (smt FM LM.A.Id_ex2 LM.Aop.Id20 LM.FunctionSet\<Phi> LM.Impl.BiF.ntExists LM.Impl_dom LM.M.AxA.Ex2 RightClosedStr.FunctionSet\<Psi> assms fst_conv snd_conv)

interpretation DeltaNatId: naturalTransformationViaIdentities domain codomain composition nonex
                         domain codomain composition nonex LM.A.map "\<lambda>f. ((f-\<circ>\<bottom>\<^sub>m)-\<circ>\<bottom>\<^sub>m)" \<delta>
  apply unfold_locales 
  using FM LM.Impl.BiF.ntExists LM.M.AxA.Ex2 apply blast
  using LM.Impl.BiF.nntExists LM.M.AxA.Ex2 apply blast
  apply (smt Delta20 Delta3 LM.A.ExDomCod(1) LM.A.S3 LM.Aop.S6 LM.Aop.double_cod LM.Impl.BiF.nntExists LM.M.AxA.Ex2)
  apply (metis FM LM.Aop.ExDomCod(2) LM.Aop.dom_cod LM.Impl.BiF.nntExists LM.Impl.BiF.ntExists LM.Impl.BiF.pres2 LM.Impl_dom LM.M.AxA.Ex2 fst_conv snd_conv)
  apply (metis FM LM.Aop.S6 LM.Impl.BiF.nntExists LM.Impl.BiF.preserves_comp LM.M.AxA.Ex2 fst_conv snd_conv)
  using Delta3 LM.A.from_hom_set_def LM.Aop.map_def apply presburger
  by (metis Delta20 LM.A.ExDomCod(1) LM.A.Ex_two_ob1 LM.A.Ex_two_ob2 LM.Aop.S6 LM.Aop.map_def LM.Impl.BiF.nntExists LM.M.AxA.Ex2)

interpretation DeltaNat: naturalTransformation domain codomain composition nonex
                         domain codomain composition nonex LM.A.map "\<lambda>f. Impl(Impl(f,\<bottom>\<^sub>m),\<bottom>\<^sub>m)" DeltaNatId.map 
  using DeltaNatId.naturalTransformation_axioms by blast

theorem DeltaNatTh: 
  shows "naturalTransformation domain codomain composition nonex
                         domain codomain composition nonex LM.A.map (\<lambda>f. Impl(Impl(f,\<bottom>\<^sub>m),\<bottom>\<^sub>m)) DeltaNatId.map"
  using DeltaNatId.naturalTransformation_axioms by blast

subsection \<open>Universal property of closed structure\<close>

abbreviation Ev :: "'a * 'a => 'a" 
where "Ev AB \<equiv> \<Psi> (fst AB) (snd AB) (fst AB -\<circ> snd AB)"

lemma LCS1: 
  assumes "((LM.A.IdEx x) \<and> (LM.A.IdEx y))"
  shows "((Ev(x,y)):(x\<otimes>(x-\<circ>y))\<rightarrow>\<^sub>Ay)"
  by (smt LM.Aop.Id20 LM.FunctionSet\<Psi> LM.Impl.BiF.ntExists LM.Impl_dom LM.M.AxA.Ex2 assms fst_conv snd_conv)

lemma LCS2: 
  assumes "((x:(a\<otimes>b)\<rightarrow>\<^sub>Ac) \<and> (LM.A.Id a) \<and> (LM.A.Id b))"
  shows "(\<exists>!h. ((h:b\<rightarrow>\<^sub>A(a-\<circ>c)) \<and> (x \<simeq> Ev(a,c)\<cdot>(a\<otimes>h))))"
proof
  let ?a = "\<Phi> a b x "
  have 1: "(?a:b\<rightarrow>\<^sub>A(a-\<circ>c))" by (metis LM.A.Id_ex LM.FunctionSet\<Phi> LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp assms)
  have 01: "((LM.A.from_hom_seta (Impl(a,c)) (Impl(a,c)) (Impl(a,c))) \<and> LM.A.Id a \<and> LM.A.Id c) \<and> ((cod ?a) = (Impl(a,c)))" by (metis "1" LM.A.Id2 LM.Aop.Id40 LM.Aop.double_dom assms)
  have 2: "x \<simeq> Ev(a,c)\<cdot>(T(a,?a))" using NaturalityInvB by (metis "01" "1" LM.A.Id_ex LM.A.S1 LM.A.S6 LM.BijectionOne LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp assms fst_conv snd_conv)
  then show "((LM.A.from_hom_seta ?a b (Impl(a,c))) \<and> (x \<simeq> Ev(a,c)\<cdot>(T(a,?a))))" using 1 by blast
  fix h
  assume "((LM.A.from_hom_seta h b (Impl(a,c))) \<and> (x \<simeq> Ev(a,c)\<cdot>(T(a,h))))"
  then have 3: "h \<^bold>= \<Phi> a b x" using NaturalityInvB by (metis "01" LM.A.Id_ex LM.A.S6 LM.BijectionTwo LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp assms fst_conv snd_conv)
  then show "h \<^bold>= \<Phi> a b x" by blast
qed

lemma LCS31: 
  assumes "((LM.A.IdEx a) \<and> (E g))"
  shows "((a-\<circ>g):(a -\<circ> dom g)\<rightarrow>\<^sub>A(a-\<circ> cod g)) \<and> (g\<cdot>Ev(a,dom g)) \<simeq> (Ev(a,cod g)\<cdot>T(a,Impl(a,g)))"
proof-
  have 1: "(LM.A.from_hom_seta (Impl(a,g)) (Impl(a,dom g)) (Impl(a,cod g)))" by (metis (no_types, hide_lams) LM.A.Ex_from_hom_set LM.A.from_hom_set_def LM.Aop.dom_cod LM.Impl.BiF.ntExists LM.Impl.BiF.pres1 LM.Impl.BiF.pres2 LM.M.T.BiF.reflects_morp LM.M.tensor_codomain assms fst_conv snd_conv)
  have 2: "(g\<cdot>Ev(a,dom g)) \<simeq> (Ev(a,cod g)\<cdot>T(a,Impl(a,g)))" by (smt "1" LM.A.Id_ex2 LM.A.S3 LM.A.S6 LM.Aop.S6 LM.Aop.cod_dom NaturalityInvB NaturalityInvC assms fst_conv snd_conv)
  thus ?thesis using 1 by blast
qed

lemma LCS3: 
  shows "((LM.A.IdEx a) \<and> (E g)) \<longrightarrow> (((a-\<circ>g):(a -\<circ> dom g)\<rightarrow>\<^sub>A(a -\<circ> cod g)) \<and> (g\<cdot>Ev(a,dom g)) \<simeq> (Ev(a,cod g)\<cdot>(a\<otimes>(a-\<circ>g))))"
  using LCS31[where ?a = \<open>a\<close> and ?g = \<open>g\<close>] Free_Impl[where ?A = \<open>((LM.A.IdEx a) \<and> (E g))\<close> and ?B = \<open>((LM.A.from_hom_set (Impl(a,g)) (Impl(a,dom g)) (Impl(a,cod g))) \<and> (g\<cdot>Ev(a,dom g)) \<simeq> (Ev(a,cod g)\<cdot>T(a,Impl(a,g))))\<close>] 
  using LM.A.from_hom_set_def by blast

section \<open>Intuitionistic Linear Logic Rules\<close>

lemma RuleIdEx: 
  assumes "LM.A.IdEx a" 
  shows "a:a\<rightarrow>\<^sub>Aa" 
  using LM.A.Id30 assms by blast

lemma RuleExchange: 
  assumes "f:(((\<Gamma>\<otimes>(A\<otimes>B))\<otimes>\<Delta>))\<rightarrow>\<^sub>AC" and "LM.A.Id A" and "LM.A.Id B" and "LM.A.Id \<Gamma>" and "LM.A.Id \<Delta>"
  shows "(f\<cdot>(((\<Gamma>\<otimes>\<gamma>(B,A))\<otimes>\<Delta>))):(((\<Gamma>\<otimes>(B\<otimes>A))\<otimes>\<Delta>))\<rightarrow>\<^sub>AC"
proof-
  have 1: "LM.A.from_hom_seta (\<gamma>(B,A)) (T(B,A)) (T(A,B))" by (smt LM.A.Id_def LM.A.Id_hom LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp LM.M.tensor_codomain LM.M.tensor_ide Sym.Braid.Br.\<eta>.presCod Sym.Braid.Br.\<eta>.presDom assms(1) assms(2) assms(3) fst_conv snd_conv)
  then have 2: "LM.A.from_hom_seta (T(\<Gamma>,\<gamma>(B,A))) (T(\<Gamma>,T(B,A))) (T(\<Gamma>,T(A,B)))" by (smt LM.A.FHS LM.A.Id_def LM.A.Id_hom LM.Aop.ExDomCod(1) LM.M.AxA.Ex2 LM.M.T.BiF.pres1 LM.M.T.BiF.reflects_morp LM.M.tensor_codomain assms(1) assms(4) fst_conv snd_conv)
  then have 3: "LM.A.from_hom_seta (T(T(\<Gamma>,\<gamma>(B,A)),\<Delta>)) (T(T(\<Gamma>,T(B,A)),\<Delta>)) (T(T(\<Gamma>,T(A,B)),\<Delta>))" by (smt LM.A.FHS LM.A.Id_def LM.A.Id_hom LM.Aop.ExDomCod(1) LM.M.AxA.Ex2 LM.M.T.BiF.pres1 LM.M.T.BiF.reflects_morp LM.M.tensor_codomain assms(1) assms(5) fst_conv snd_conv)
  thus "LM.A.from_hom_seta (f\<cdot>(T(T(\<Gamma>,\<gamma>(B,A)),\<Delta>))) (T(T(\<Gamma>,T(B,A)),\<Delta>)) C" by (metis "2" LM.A.Id_def LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp LM.M.tensor_morph assms(1) assms(5))
qed

lemma RuleCut: 
  assumes "f:\<Gamma>\<rightarrow>\<^sub>AA" and "g:(A\<otimes>\<Delta>)\<rightarrow>\<^sub>AB" and "LM.A.Id \<Delta>"
  shows "LM.A.from_hom_seta (g\<cdot>T(f,\<Delta>)) (T(\<Gamma>,\<Delta>)) B" 
  using LM.A.Id_ex LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp LM.M.tensor_morph assms(1) assms(2) assms(3) by blast

lemma RuleTensorR: 
  assumes "f:\<Gamma>\<rightarrow>\<^sub>AA" and "g:\<Delta>\<rightarrow>\<^sub>AB"
  shows "(f\<otimes>g):(\<Gamma>\<otimes>\<Delta>)\<rightarrow>\<^sub>A(A\<otimes>B)"
  by (metis LM.A.FHS LM.M.tensor_codomain LM.M.tensor_domain assms(1) assms(2))

lemma RuleTensorL: 
  assumes "f:(((\<Gamma>\<otimes>A)\<otimes>B))\<rightarrow>\<^sub>AC" and "LM.A.Id A" and "LM.A.Id B" and "LM.A.Id \<Gamma>" 
  shows "(f\<cdot>(\<alpha>\<^sup>-\<^sup>1(\<Gamma>,A,B))):((\<Gamma>\<otimes>(A\<otimes>B)))\<rightarrow>\<^sub>AC"
  by (metis (no_types, lifting) LM.A.Id3 LM.A.Id_def LM.A.S3 LM.A.cod_of_comp LM.A.dom_of_comp LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp LM.M.T.TAT_simp LM.M.T.TTA_simp RuleTensorR Sym.Braid.\<alpha>_inv.presCod Sym.Braid.\<alpha>_inv.presDom assms(1) assms(2) assms(3) assms(4))

lemma RuleImplicationR: 
  assumes "f:(\<Gamma>\<otimes>A)\<rightarrow>\<^sub>AB" and "LM.A.Id A" and "LM.A.Id \<Gamma>" 
  shows "(\<Phi>r \<Gamma> A f):\<Gamma>\<rightarrow>\<^sub>A(A-\<circ>B)" 
  using RightClosedStr.FunctionSet\<Phi> assms(1) assms(2) assms(3) by blast

lemma RuleImplicationL: 
  assumes "f:\<Gamma>\<rightarrow>\<^sub>AA" and "g:B\<otimes>\<Delta>\<rightarrow>\<^sub>AC" and "LM.A.Id B" and "LM.A.Id \<Delta>" 
  shows "((g\<cdot>(Ev(A,B)\<otimes>\<Delta>))\<cdot>((f\<otimes>(A-\<circ>B))\<otimes>\<Delta>)):((\<Gamma>\<otimes>(A-\<circ>B))\<otimes>\<Delta>)\<rightarrow>\<^sub>AC"
  by (smt LCS1 LCS31 LM.A.Id3 LM.Aop.cod_dom LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp RuleCut RuleTensorR assms(1) assms(2) assms(3) assms(4))

lemma RuleUnitR: 
  shows "LM.A.IdEx \<e>" 
  using LM.M.unit_object by blast

lemma RuleUnitL: 
  assumes "f:(\<Gamma>\<otimes>\<Delta>)\<rightarrow>\<^sub>AA" and "LM.A.Id \<Gamma>" and "LM.A.Id \<Delta>" 
  shows "(f\<cdot>(\<Gamma>\<otimes>(\<mu> \<Delta>))):(\<Gamma>\<otimes>(\<e>\<otimes>\<Delta>))\<rightarrow>\<^sub>AA"
proof-
  have 1: "(\<mu> \<Delta>):(\<e>\<otimes>\<Delta>)\<rightarrow>\<^sub>A\<Delta>" by (metis LCS2 LM.A.Id3 LM.A.Id_def LM.A.S3 LM.Ae1 LM.Ae8 LM.M.\<mu>.\<eta>.presDom RuleTensorR RuleUnitR assms(1) assms(2) assms(3))
  have 2: "(\<Gamma>\<otimes>(\<mu> \<Delta>)):(\<Gamma>\<otimes>(\<e>\<otimes>\<Delta>))\<rightarrow>\<^sub>A(\<Gamma>\<otimes>\<Delta>)" by (metis "1" LM.A.Id3 LM.A.Id_ex LM.M.AxA.Ex2 LM.M.T.BiF.reflects_morp RuleTensorR assms(1) assms(2))
  then have 3: "(f\<cdot>(\<Gamma>\<otimes>(\<mu> \<Delta>))):(\<Gamma>\<otimes>(\<e>\<otimes>\<Delta>))\<rightarrow>\<^sub>AA" using LM.A.S3 LM.A.cod_of_comp LM.A.dom_of_comp assms(1) by presburger
  thus ?thesis by blast
qed

lemmas ILL = RuleIdEx RuleExchange RuleCut RuleTensorR RuleTensorL RuleImplicationR RuleImplicationL

end

sublocale SymmetricMonClosedCat \<subseteq> RightClosedMonCatBifunctor domain codomain composition * T \<alpha> \<mu> \<rho> \<e> Impr \<Phi>r \<Psi>r
  using RightMonoidalStructure by linarith

sublocale SymmetricMonClosedCat \<subseteq> LeftClosedMonCatBifunctor domain codomain composition * T \<alpha> \<mu> \<rho> \<e> Impl \<Phi> \<Psi>
  by (simp add: LM.LeftClosedMonCatBifunctor_axioms)

end