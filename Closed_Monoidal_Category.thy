theory Closed_Monoidal_Category
  imports Monoidal_Category

begin

section \<open>Left monoidal closed category\<close>

locale LeftClosedMonCatBifunctor = 
  A: category domain codomain composition nonex +
  Aop: opposite_category domain codomain composition nonex +
  M: Monoidal_Category domain codomain composition nonex T \<alpha> \<mu> \<rho> \<e> +
  Impl: biAopAEndoFunctor domain codomain composition nonex Impl 
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
  Impl :: "'a * 'a \<Rightarrow> 'a" and 
  \<Phi> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and 
  \<Psi> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" +
assumes 
  FunctionSet\<Phi>: "((f:(a\<otimes>b)\<rightarrow>\<^sub>Ac) \<and> A.IdEx a \<and> A.IdEx b) \<longrightarrow> 
                 ((\<Phi> a b f):b\<rightarrow>\<^sub>A(Impl(a,c)))" and
  FunctionSet\<Psi>: "((g:b\<rightarrow>\<^sub>A(Impl(a,c))) \<and> A.IdEx a \<and> A.IdEx c) \<longrightarrow> 
                 ((\<Psi> a c g):(a\<otimes>b)\<rightarrow>\<^sub>Ac)" and
  BijectionOne: "((f:(a\<otimes>b)\<rightarrow>\<^sub>Ac) \<and> A.IdEx a \<and> A.IdEx b) \<longrightarrow> 
                 (\<Psi> a c (\<Phi> a b f) \<simeq> f)" and 
  BijectionTwo: "((g:b\<rightarrow>\<^sub>A(Impl(a,c))) \<and> A.IdEx a \<and> A.IdEx c) \<longrightarrow> 
                 (\<Phi> a b (\<Psi> a c g) \<simeq> g)" and
  NaturalityD\<Phi>: "((f:(a\<otimes>b)\<rightarrow>\<^sub>Ac) \<and> A.IdEx a \<and> A.IdEx b \<and> ((cod x) = a) \<and> ((cod y) = b) \<and> ((dom z) = c)) \<longrightarrow>
                (\<Phi> (dom x) (dom y) (z\<cdot>(f\<cdot>(x\<otimes>y)))) \<simeq> (Impl(x,z))\<cdot>((\<Phi> a b f)\<cdot>y)" 

begin 

abbreviation Implication (infix "-\<circ>" 56) 
  where "(x -\<circ> y) \<equiv> Impl(x,y)"

lemma NaturalityA: 
  shows "((f:(a\<otimes>b)\<rightarrow>\<^sub>Ac) \<and> A.IdEx a \<and> A.IdEx b \<and> ((cod x) = a)) \<longrightarrow> 
         (\<Phi> (dom x) b (f \<cdot> (x\<otimes>b)) \<simeq> (x-\<circ>c) \<cdot> (\<Phi> a b f))"
  using NaturalityD\<Phi>[where y = \<open>b\<close> and z = \<open>c\<close>] 
  by (smt A.S1 A.S5 A.S6 Aop.ExDomCod(1) Aop.cod_dom Aop.dom_cod LeftClosedMonCatBifunctor.FunctionSet\<Phi> LeftClosedMonCatBifunctor_axioms M.tensor_morph)

lemma NaturalityB: 
  shows "((f:(a\<otimes>b)\<rightarrow>\<^sub>Ac) \<and> A.IdEx a \<and> A.IdEx b \<and> ((cod y) = b)) \<longrightarrow> 
         ((\<Phi> a (dom y) (f \<cdot> (a\<otimes>y)) \<simeq> (\<Phi> a b f)\<cdot>y))"
  using NaturalityD\<Phi>[where x = \<open>a\<close> and z = \<open>c\<close>] 
  by (smt A.FHS A.S3 A.S4 A.S5 A.S6 M.tensor_codomain)

lemma NaturalityC: 
  shows "((f:(a\<otimes>b)\<rightarrow>\<^sub>Ac) \<and> A.IdEx a \<and> A.IdEx b \<and> ((dom z) = c)) \<longrightarrow> 
         (\<Phi> a b (z \<cdot> f) \<simeq> (a-\<circ>z)\<cdot>(\<Phi> a b f))"
  using NaturalityD\<Phi>[where x = \<open>a\<close> and y = \<open>b\<close>] 
  by (metis A.S5 Aop.Id40 Aop.S2 FunctionSet\<Phi>)

lemma Impl_dom: 
  assumes "E (Impl(x,y))" 
  shows "(dom (Impl(x,y))) = Impl(cod x, dom y)"
  by (metis A.S3 A.S5 Impl.BiF.pres1 assms fst_eqD snd_eqD)

lemma Impl_morph:
  assumes "A.from_hom_seta f a' a" and "A.from_hom_seta x b (Impl(a,c))" and "A.IdEx c" 
  shows "A.from_hom_seta (Impl(f,c)\<cdot>x) b (Impl(a',c))" 
  by (smt A.S1 A.S3 A.cod_of_comp A.dom_of_comp Aop.Id20 Impl.BiF.ntExists Impl.BiF.pres2 Impl_dom M.AxA.Ex2 assms(1) assms(2) assms(3) fst_eqD snd_eqD)

lemma Adj1Surj: 
  assumes "A.IdEx a" 
  shows "((A.from_hom_seta h b (Impl(a,c))) \<and> (A.Id c)) \<longrightarrow> (\<exists>f. A.from_hom_seta f (T(a,b)) c \<and> (\<Phi> a b f) = h)"
  by (smt A.Id_def BijectionTwo FunctionSet\<Psi> LeftClosedMonCatBifunctor_axioms LeftClosedMonCatBifunctor_def M.AxA.Ex2 assms biAopAEndoFunctor_def biFunctor_def functorCat.nexists)

lemma Ae1: 
  assumes "A.IdEx a" 
  shows "(\<Phi> \<e> a (\<mu> a)):a\<rightarrow>\<^sub>A(\<e>-\<circ>a)"
  by (metis (no_types, lifting) Aop.Id20 Aop.map_def FunctionSet\<Phi> M.\<mu>.F.ntExists M.\<mu>.F.pres1 M.\<mu>.\<eta>.presCod M.\<mu>.\<eta>.presDom M.unit_object assms)

lemma Ae2: 
  assumes "A.IdEx a" 
  shows "\<exists>f. (f:a\<rightarrow>\<^sub>A(\<e>-\<circ>a))"
  using Ae1 assms by blast

lemma Ae3: 
  assumes "A.IdEx a" 
  shows "\<Phi> \<e> (\<e>-\<circ>a) (\<Psi> \<e> a (\<e>-\<circ>a)) \<simeq> \<e>-\<circ>a" 
  by (metis Ae2 Aop.Id30 Aop.double_dom BijectionTwo M.unit_object assms)

lemma Ae4: 
  assumes "A.IdEx a" 
  shows "(A.inv (\<mu> (\<e>-\<circ>a))):(\<e>-\<circ>a)\<rightarrow>\<^sub>A(\<e>\<otimes>(\<e>-\<circ>a))" 
  by (smt A.S3 A.inv_ex A.inv_ex2 Ae2 Aop.Id20 Aop.map_def LeftClosedMonCatBifunctor.Impl_dom LeftClosedMonCatBifunctor_axioms M.\<mu>.F.functorCat_axioms M.\<mu>.\<eta>.naturalTransformation_axioms M.\<mu>.comp_iso M.unit_object assms functorCat.pres1 naturalTransformation.presCod naturalTransformation.presDom)

lemma Ae5: 
  assumes "A.IdEx a" 
  shows "(\<Psi> \<e> a (Impl(\<e>,a))):(\<e>\<otimes>(\<e>-\<circ>a))\<rightarrow>\<^sub>Aa" 
  by (metis Ae4 Aop.Id20 FunctionSet\<Psi> LeftClosedMonCatBifunctor.Impl_dom LeftClosedMonCatBifunctor_axioms M.unit_object assms)

lemma Ae6: 
  assumes "A.IdEx a" 
  shows "((\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>(A.inv (\<mu> (\<e>-\<circ>a)))):(\<e>-\<circ>a)\<rightarrow>\<^sub>Aa"
  using Ae4 Ae5 A.S3 A.cod_of_comp A.dom_of_comp assms by presburger

lemma Ae7:
  assumes "A.IdEx a" 
  shows "(((\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>(A.inv (\<mu> (\<e>-\<circ>a))))\<cdot>(\<Phi> \<e> a (\<mu> a))):a\<rightarrow>\<^sub>Aa"
  using A.S3 A.cod_of_comp A.dom_of_comp Ae1 Ae6 assms by presburger

lemma Ae8: 
  assumes "A.IdEx a" 
  shows "(\<Phi> \<e> a (\<mu> a))\<cdot>(\<mu> a) \<simeq> (\<mu> (\<e>-\<circ>a))\<cdot>(\<e>\<otimes>(\<Phi> \<e> a (\<mu> a)))"
  by (smt A.S2 A.S5 A.S6 Ae1 Aop.map_def M.\<mu>.\<eta>.naturality M.\<mu>.\<eta>.presCod M.\<mu>.\<eta>.preserves_comp assms)

lemma Ae9: 
  assumes "A.IdEx a"
  shows "A.IdEx ((A.inv (\<mu> a))\<cdot>(\<mu> a))"
  using A.Id_ex A.inv_ex A.invcheck1 M.\<mu>.comp_iso assms by blast

lemma Ae10: 
  assumes "A.IdEx a"
  shows "A.IdEx ((\<mu> a)\<cdot>(A.inv (\<mu> a)))"
  by (metis A.I_dom A.Inv_I2 A.inv_ex2 M.\<mu>.comp_iso assms)

lemma Ae11: 
  assumes "A.IdEx a" 
  shows "\<Phi> \<e> a (\<mu> a) \<simeq> ((\<mu> (\<e>-\<circ>a))\<cdot>(\<e>\<otimes>(\<Phi> \<e> a (\<mu> a))))\<cdot>(A.inv (\<mu> a))"
  by (smt A.S3 A.S4 A.S5 Ae8 Ae10 Aop.dom_cod assms)

lemma Ae12: 
  assumes "A.IdEx a" 
  shows "(A.inv (\<mu> (\<e>-\<circ>a)))\<cdot>(\<Phi> \<e> a (\<mu> a)) \<simeq> (\<e>\<otimes>(\<Phi> \<e> a (\<mu> a)))\<cdot>(A.inv (\<mu> a))"
  using Ae9 
  by (smt A.S3 A.S4 A.S5 A.S6 Ae4 Ae11 Aop.dom_cod Aop.map_def assms)

lemma Ae13: 
  assumes "A.IdEx a" 
  shows "(\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>((A.inv (\<mu> (\<e>-\<circ>a)))\<cdot>(\<Phi> \<e> a (\<mu> a))) \<simeq> (\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>((\<e>\<otimes>(\<Phi> \<e> a (\<mu> a)))\<cdot>(A.inv (\<mu> a)))"
  by (metis A.S3 A.cod_of_comp Ae12 Ae4 Ae5 assms)

lemma Ae14: 
  assumes "A.IdEx a" 
  shows "(\<Phi> \<e> a ((\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>(\<e>\<otimes>(\<Phi> \<e> a (\<mu> a))))) \<simeq> (\<e>-\<circ>a)\<cdot>(\<Phi> \<e> a (\<mu> a))" 
  by (smt Ae1 Ae3 Ae5 Aop.dom_cod Impl_dom M.unit_object NaturalityB assms) 

lemma Ae15: 
  assumes "A.IdEx a" 
  shows "(\<Phi> \<e> a ((\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>(\<e>\<otimes>(\<Phi> \<e> a (\<mu> a))))) \<simeq> (\<Phi> \<e> a (\<mu> a))"
  by (metis Ae1 Ae14 Aop.S5 assms)

lemma Ae16: 
  assumes "A.IdEx a" 
  shows "\<Psi> \<e> a (\<Phi> \<e> a ((\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>(\<e>\<otimes>(\<Phi> \<e> a (\<mu> a))))) = (\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>(\<e>\<otimes>(\<Phi> \<e> a (\<mu> a)))" 
  by (smt A.S3 A.cod_of_comp A.dom_of_comp Ae1 Ae5 BijectionOne M.\<mu>.F.pres1 M.\<mu>.F.pres2 M.tensor_arrow_2 M.unit_object assms)

lemma Ae17: 
  assumes "A.IdEx a" 
  shows "\<Psi> \<e> a (\<Phi> \<e> a (\<mu> a)) = \<mu> a" 
  by (metis A.S3 Ae1 Ae8 BijectionOne M.\<mu>.F.ntExists M.\<mu>.F.pres1 M.\<mu>.\<eta>.presDom M.unit_object assms)

lemma Ae18: 
  assumes "A.IdEx a" 
  shows "((\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>(\<e>\<otimes>(\<Phi> \<e> a (\<mu> a)))) \<simeq> (\<mu> a)"
  using Ae16 Ae17 Ae15 
  by (metis A.category_axioms M.\<mu>.comp_iso assms category.IsoE)

lemma Ae19: 
  assumes "A.IdEx a" 
  shows "(\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>((A.inv (\<mu> (\<e>-\<circ>a)))\<cdot>(\<Phi> \<e> a (\<mu> a))) \<simeq> a" 
  by (metis A.S4 A.dom_of_comp Ae1 Ae13 Ae15 Ae16 Ae17 Ae10 assms)

lemma Ae20: 
  assumes "A.IdEx a" 
  shows "(\<Phi> \<e> a (\<mu> a))\<rightleftharpoons>((\<Psi> \<e> a (\<e>-\<circ>a))\<cdot>((A.inv (\<mu> (\<e>-\<circ>a)))))"
  using Ae19 NaturalityB 
  by (smt A.Ex_two_ob1 A.Id_ex2 A.S3 A.S4 A.S5 A.S6 A.dom_of_comp Ae3 Ae6 Ae9 Aop.map_def M.\<mu>.F.ntExists M.\<mu>.\<eta>.naturality M.\<mu>.\<eta>.ntExists M.\<mu>.\<eta>.preserves_comp M.unit_object assms)

lemma Ae21: 
  assumes "A.IdEx a" 
  shows "A.Iso_a (\<Phi> \<e> a (\<mu> a))" 
  using A.Ex_two_ob1 Ae20 assms by blast

lemma Ae: 
  assumes "A.IdEx a" 
  shows "A.isomorphic a (\<e>-\<circ>a)" 
  using Ae21
  using A.IsoE A.Iso_def Ae1 assms 
  by meson

end

section \<open>Right monoidal closed category\<close>

locale RightClosedMonCatBifunctor = 
A: category domain codomain composition nonex +
Aop: opposite_category domain codomain composition nonex +
M: Monoidal_Category domain codomain composition nonex T \<alpha> \<mu> \<rho> \<e> +
Impr: biAopAEndoFunctor domain codomain composition nonex Impr 
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
Impr :: "'a * 'a \<Rightarrow> 'a" and 
\<Phi>r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and 
\<Psi>r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" +
assumes 
FunctionSet\<Phi>: "((f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (A.Id a) \<and> (A.Id b)) \<longrightarrow> 
               ((\<Phi>r b a f):b\<rightarrow>\<^sub>A(Impr(a,c)))" and
FunctionSet\<Psi>: "((g:b\<rightarrow>\<^sub>A(Impr(a,c))) \<and> (A.Id a) \<and> (A.Id c)) \<longrightarrow> 
               ((\<Psi>r a c g):(b\<otimes>a)\<rightarrow>\<^sub>Ac)" and
BijectionOne: "((f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (A.IdEx a) \<and> (A.IdEx b)) \<longrightarrow> 
               (\<Psi>r a c (\<Phi>r b a f) = f)" and 
BijectionTwo: "((g:b\<rightarrow>\<^sub>A(Impr(a,c))) \<and> (A.IdEx a) \<and> (A.IdEx c)) \<longrightarrow> 
               (\<Phi>r b a (\<Psi>r a c g) = g)" and
NaturalityD\<Phi>: "((f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (A.IdEx a) \<and> (A.IdEx b) \<and> ((cod x) = a) \<and> ((cod y) = b) \<and> ((dom z) = c)) \<longrightarrow>
              (\<Phi>r (dom y) (dom x) (z\<cdot>(f\<cdot>(y\<otimes>x))) \<simeq> (Impr(x,z))\<cdot>((\<Phi>r b a f)\<cdot>y))"

begin 

abbreviation RImplication (infix "\<circ>-" 56)
  where "x \<circ>- y \<equiv> Impr(x,y)"

lemma NaturalityA: 
  shows "((f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (A.IdEx a) \<and> (A.IdEx b) \<and> ((cod x) = a)) \<longrightarrow> 
              ((\<Phi>r b (dom x) (f \<cdot> (b\<otimes>x)) \<simeq> (x\<circ>-c)\<cdot>(\<Phi>r b a f)))"
  by (smt A.FHS A.Id_ex2 A.S3 A.S5 A.S6 A.cod_of_comp M.tensor_codomain NaturalityD\<Phi> RightClosedMonCatBifunctor.FunctionSet\<Phi> RightClosedMonCatBifunctor_axioms)

lemma NaturalityB: 
  shows "((f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (A.IdEx a) \<and> (A.IdEx b) \<and> ((cod y) = b)) \<longrightarrow> 
              ((\<Phi>r (dom y) a (f \<cdot> (y\<otimes>a)) \<simeq> (\<Phi>r b a f)\<cdot>y))"
  using NaturalityD\<Phi>[where x = \<open>a\<close> and z = \<open>c\<close>] 
  by (smt A.Id_ex2 A.S1 A.S4 A.S6 Aop.ExDomCod(1) Aop.cod_dom Aop.dom_cod M.tensor_morph RightClosedMonCatBifunctor.FunctionSet\<Phi> RightClosedMonCatBifunctor_axioms)

lemma NaturalityC: 
  shows "((f:(b\<otimes>a)\<rightarrow>\<^sub>Ac) \<and> (A.IdEx a) \<and> (A.IdEx b) \<and> ((dom z) = c)) \<longrightarrow> 
              ((\<Phi>r b a (z \<cdot> f) \<simeq> (a\<circ>-z)\<cdot>(\<Phi>r b a f)))"
  using NaturalityD\<Phi>[where x = \<open>a\<close> and y = \<open>b\<close>] 
  by (smt A.S1 A.S5 Aop.Id40 RightClosedMonCatBifunctor.NaturalityB RightClosedMonCatBifunctor_axioms)

end

end