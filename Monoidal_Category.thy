theory Monoidal_Category
  imports Natural_Transformations

begin

section \<open>Binary endofunctors\<close>

locale biEndoFunctor = 
A: category domain codomain composition nonex +
AxA: productCategory domain codomain composition nonex domain codomain composition nonex +
AxAxA: productCategory domain codomain composition nonex AxA.Dom AxA.Cod AxA.Composition AxA.Nonex +
BiF: biFunctor domain codomain composition nonex domain codomain composition nonex domain codomain composition nonex T
for 
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  T :: "'a * 'a \<Rightarrow> 'a"

begin 

lemma True 
  nitpick [satisfy, user_axioms, expect=genuine, card 'a=2,card 'b=4,card 'c=8] oops

definition TTA
  where "TTA x \<equiv> T (T (fst x, fst (snd x)), snd (snd x))"

lemma TTA_is_functor:
  shows "functorCat AxAxA.Dom AxAxA.Cod AxAxA.Composition AxAxA.Nonex domain codomain composition nonex TTA"
  using TTA_def
  apply unfold_locales
  apply (metis AxA.Ex AxAxA.Ex BiF.ntExists prod.collapse)
  apply (metis AxA.Ex AxAxA.Ex BiF.reflects_morp prod.collapse)
  apply (metis AxA.Ex BiF.nntExists BiF.pres1 fst_conv snd_conv)
  apply (metis AxA.Ex BiF.nntExists BiF.pres2 fst_conv snd_conv)
  by (metis AxA.Ex BiF.nntExists BiF.pres3 fst_conv snd_conv)

lemma TTA_simp [simp]:
  shows "(TTA (x,y,z)) \<cong> (T (T (x,y),z))" 
  by (simp add: TTA_def)

definition TAT
  where "TAT x \<equiv> T (fst x, T (fst (snd x), snd (snd x)))"

lemma TAT_is_functor: 
  shows "functorCat AxAxA.Dom AxAxA.Cod AxAxA.Composition AxAxA.Nonex domain codomain composition nonex TAT"
  using TAT_def
  apply unfold_locales
  apply (metis AxA.Ex AxAxA.Ex BiF.ntExists prod.collapse)
  apply (metis AxA.Ex AxAxA.Ex BiF.reflects_morp prod.collapse)
  apply (metis AxA.Ex BiF.nntExists BiF.pres1 fst_conv snd_conv)
  apply (metis AxA.Ex BiF.nntExists BiF.pres2 fst_conv snd_conv)
  by (metis AxA.Ex BiF.nntExists BiF.pres3 fst_conv snd_conv)

lemma TAT_simp [simp]: 
  shows "TAT (x,y,z) \<cong> T (x, T (y,z))" 
  by (simp add: TAT_def)

definition tensor_wl_object
  where "tensor_wl_object a \<equiv> \<lambda>x. T (a,x)"

end

locale biAopAEndoFunctor = 
A: category domain codomain composition nonex +
Aop: opposite_category domain codomain composition nonex +
AopxA: productCategory Aop.domop Aop.codop Aop.compositionop nonex domain codomain composition nonex +
BiF: biFunctor Aop.domop Aop.codop Aop.compositionop nonex domain codomain composition nonex domain codomain composition nonex Il
for 
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  Il :: "'a * 'a \<Rightarrow> 'a"
begin 

end

section \<open>Monoidal category\<close>

locale Monoidal_Category = 
A: category domain codomain composition nonex + 
AxA: productCategory domain codomain composition nonex domain codomain composition nonex +
AxAxA: productCategory domain codomain composition nonex AxA.Dom AxA.Cod AxA.Composition AxA.Nonex +
T: biEndoFunctor domain codomain composition nonex T +
\<alpha>: naturalIsomorphism AxAxA.Dom AxAxA.Cod AxAxA.Composition AxAxA.Nonex domain codomain composition nonex T.TTA T.TAT \<alpha> +
\<mu>: naturalIsomorphism domain codomain composition nonex domain codomain composition nonex "\<lambda>x::'a. T (\<e>,x)" A.map \<mu> +
\<rho>: naturalIsomorphism domain codomain composition nonex domain codomain composition nonex "\<lambda>x::'a. T (x,\<e>)" A.map \<rho> 
for 
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  T :: "'a * 'a \<Rightarrow> 'a" and 
  \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a" and
  \<mu> :: "'a \<Rightarrow> 'a" and 
  \<rho> :: "'a \<Rightarrow> 'a" and
  \<e> :: "'a" +
assumes 
  unit_object: "A.IdEx \<e>" and
  triangle: "((A.Id x) \<and> (A.Id y)) \<longrightarrow> (((T (x, (\<mu> y)))\<cdot>(\<alpha>(x,\<e>,y))) \<cong> (T(\<rho> x,y)))" and
  pentagon: "((A.Id x) \<and> (A.Id y) \<and> (A.Id z) \<and> (A.Id w)) 
             \<longrightarrow> (((T (x,\<alpha>(y,z,w))) \<cdot> ((\<alpha>(x,T(y,z),w)) \<cdot> (T(\<alpha>(x,y,z),w)))) \<cong> (\<alpha>(x,y,T(z,w))) \<cdot> (\<alpha>(T(x,y),z,w)))"

begin

(* lemma True 
  nitpick [satisfy, user_axioms, expect=genuine] oops *)

abbreviation TensorProd (infix "\<otimes>" 56) 
  where "x\<otimes>y \<equiv> T(x,y)"

abbreviation from_hom_seta ("(_):(_)\<rightarrow>\<^sub>A(_)")
  where "(x:a\<rightarrow>\<^sub>Ab) \<equiv> A.from_hom_seta x a b" 

lemma tensor_arrow[simp]: 
  assumes "A.from_hom_set x a b" and "A.from_hom_set y c d" 
  shows "A.from_hom_set (x\<otimes>y) (a\<otimes>c) (b\<otimes>d)" 
  by (metis A.from_hom_set_def AxA.Ex T.BiF.ntExists T.BiF.pres1 T.BiF.pres2 assms(1) assms(2) fst_conv snd_conv)

lemma tensor_arrow_2[simp]: 
  assumes "E x" and "E y" 
  shows "E (x\<otimes>y)" 
  using AxA.Ex T.BiF.ntExists assms(1) assms(2) by blast

lemma tensor_domain[simp]: 
  assumes "A.from_hom_set x a b" and "A.from_hom_set y c d"
  shows "(domain (x\<otimes>y)) \<simeq> (a\<otimes>c)" 
  by (metis A.from_hom_set_def T.BiF.pres1 assms(1) assms(2) fst_conv snd_conv tensor_arrow_2)

lemma tensor_codomain[simp]: 
  assumes "A.from_hom_set x a b" and "A.from_hom_set y c d"
  shows "(codomain (x\<otimes>y)) \<simeq> (b\<otimes>d)"
  by (metis A.from_hom_set_def T.BiF.pres2 assms(1) assms(2) fst_conv snd_conv tensor_arrow_2)

lemma tensor_ide[simp]: 
  assumes "A.Id(x)" and "A.Id(y)" 
  shows "A.Id (x\<otimes>y)" 
  by (meson A.Id_def A.Id_hom A.S1 AxA.Ex T.BiF.nntExists assms(1) assms(2) tensor_arrow)

lemma tensor_interchange: 
  assumes "E (x\<cdot>y)" and "E (x'\<cdot>y')" 
  shows "((x\<otimes>x')\<cdot>(y\<otimes>y')) \<cong> x\<cdot>y\<otimes>x'\<cdot>y'" 
  using T.BiF.pres3 assms(1) assms(2) by auto

lemma tensor_iso[simp]: 
  assumes "Iso\<^sub>a x" and "Iso\<^sub>a y" and "E x" and "E y" 
  shows "Iso\<^sub>a (x\<otimes>y)" 
  by (smt A.Ex_two_ob1 A.Ex_two_ob2 A.Id_ex A.S4 A.S5 A.dom_of_comp AxA.Ex T.BiF.ntExists assms(1) assms(2) tensor_ide tensor_interchange)

lemma tensor_iso2[simp]: 
  assumes "Iso x" and "Iso y" and "E x" and "E y" 
  shows "Iso (x\<otimes>y)" 
  using A.Iso_def assms(1) assms(2) assms(3) assms(4) tensor_iso by auto

lemma tensor_morph: 
  assumes "f:a\<rightarrow>\<^sub>Aa'" and "A.IdEx b" and "x:(T(a',b))\<rightarrow>\<^sub>Ac" 
  shows "(x\<cdot>(f\<otimes>b)):(a\<otimes>b)\<rightarrow>\<^sub>Ac" 
  by (metis (no_types, hide_lams) A.S3 A.cod_dom A.cod_of_comp A.dom_of_comp A.from_hom_set_def assms(1) assms(2) assms(3) tensor_codomain tensor_domain)

lemma unit_tensor1: 
  assumes "A.IdEx a" and "A.IdEx b" and "A.isomorphic a b"
  shows "A.isomorphic (a\<otimes>\<e>) (b\<otimes>\<e>)" 
proof- 
  have 1: "A.isomorphic (a\<otimes>\<e>) a" 
    by (metis (no_types, hide_lams) A.ExDomCod(2) A.Iso_a A.cod_dom A.map_def \<rho>.F.pres1 \<rho>.\<eta>.presCod \<rho>.\<eta>.presDom \<rho>.comp_iso assms(1) tensor_arrow_2 unit_object)
  also have 2: "A.isomorphic (b\<otimes>\<e>) b" 
    by (metis A.ExDomCod(2) A.Iso_a A.cod_dom A.map_def \<rho>.F.pres1 \<rho>.\<eta>.presCod \<rho>.\<eta>.presDom \<rho>.comp_iso assms(2) tensor_arrow_2 unit_object)
  ultimately have 3: "A.isomorphic (a\<otimes>\<e>) (b\<otimes>\<e>)" using assms(3) oops

interpretation \<mu>_inv: inverse_natural_tr domain codomain composition nonex domain codomain composition nonex "\<lambda>x::'a. T (\<e>,x)" A.map \<mu>
  by (simp add: \<mu>.naturalIsomorphism_axioms nat_transform_impl_inverse)

interpretation \<rho>_inv: inverse_natural_tr domain codomain composition nonex domain codomain composition nonex "\<lambda>x::'a. T (x,\<e>)" A.map \<rho>
  by (simp add: \<rho>.naturalIsomorphism_axioms nat_transform_impl_inverse)

interpretation \<alpha>_inv: inverse_natural_tr AxAxA.Dom AxAxA.Cod AxAxA.Composition AxAxA.Nonex domain codomain composition nonex T.TTA T.TAT \<alpha>
  by (simp add: \<alpha>.naturalIsomorphism_axioms nat_transform_impl_inverse)

abbreviation \<mu>_inv ("\<mu>\<^sup>-\<^sup>1")
  where "\<mu>\<^sup>-\<^sup>1 \<equiv> \<mu>_inv.map"

abbreviation \<rho>_inv ("\<rho>\<^sup>-\<^sup>1")
  where "\<rho>\<^sup>-\<^sup>1 \<equiv> \<rho>_inv.map"

abbreviation \<alpha>_inv ("\<alpha>\<^sup>-\<^sup>1")
  where "\<alpha>\<^sup>-\<^sup>1 \<equiv> \<alpha>_inv.map" 

end

section \<open>Braided monoidal category\<close>

locale Braiding = 
A: category domain codomain composition nonex + 
AxA: productCategory domain codomain composition nonex domain codomain composition nonex +
AxAxA: productCategory domain codomain composition nonex AxA.Dom AxA.Cod AxA.Composition AxA.Nonex +
T: biEndoFunctor domain codomain composition nonex T + 
\<alpha>: naturalIsomorphism AxAxA.Dom AxAxA.Cod AxAxA.Composition AxAxA.Nonex domain codomain composition nonex T.TTA T.TAT \<alpha> +
Br: naturalIsomorphism AxA.Dom AxA.Cod AxA.Composition AxA.Nonex domain codomain composition nonex T T.BiF.Exch \<gamma> +
\<alpha>_inv: inverse_natural_tr AxAxA.Dom AxAxA.Cod AxAxA.Composition AxAxA.Nonex domain codomain composition nonex T.TTA T.TAT \<alpha> +
Br_inv: inverse_natural_tr AxA.Dom AxA.Cod AxA.Composition AxA.Nonex domain codomain composition nonex T T.BiF.Exch \<gamma>
for
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  T :: "'a * 'a \<Rightarrow> 'a" and 
  \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a" and
  \<gamma> :: "'a * 'a \<Rightarrow> 'a" +
assumes
  hexagon1: "((A.Id x) \<and> (A.Id y) \<and> (A.Id z)) \<longrightarrow> ((\<alpha>(y,z,x) \<cdot> (\<gamma>(x,T(y,z)) \<cdot> \<alpha>(x,y,z))) \<cong> 
             (T(y,\<gamma>(x,z)) \<cdot> (\<alpha>(y,x,z) \<cdot> T(\<gamma>(x,y),z))))" and
  hexagon2: "((A.Id x) \<and> (A.Id y) \<and> (A.Id z)) \<longrightarrow> ((\<alpha>_inv.map(z,x,y) \<cdot> (\<gamma>(T(x,y),z) \<cdot> \<alpha>_inv.map(x,y,z))) \<cong> 
             (T(\<gamma>(x,z),y) \<cdot> (\<alpha>_inv.map(x,z,y) \<cdot> T(x,\<gamma>(y,z)))))" 
begin

end

locale Braided_Mon_Cat =
  M: Monoidal_Category domain codomain composition nonex T \<alpha> \<mu> \<rho> \<e> +
  Braid: Braiding domain codomain composition nonex T \<alpha> \<gamma> 
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
  \<gamma> :: "'a * 'a \<Rightarrow> 'a"
begin 

end

section \<open>Symmetric monoidal category\<close>

locale Symmetry = 
Braid: Braiding domain codomain composition nonex T \<alpha> \<gamma>
for
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  T :: "'a * 'a \<Rightarrow> 'a" and 
  \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a" and
  \<gamma> :: "'a * 'a \<Rightarrow> 'a" +
assumes 
  symmetry: "((Braid.A.Id a) \<and> (Braid.A.Id b)) \<longrightarrow> (\<gamma>(b,a) \<cong> Braid.Br_inv.map(a,b))"

begin

end

locale Symmetric_Mon_Cat = 
  M: Monoidal_Category domain codomain composition nonex T \<alpha> \<mu> \<rho> \<e> +
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
  \<gamma> :: "'a * 'a \<Rightarrow> 'a"
begin 

lemma Dom: 
  assumes "M.A.Id a" and "M.A.Id b" 
  shows "(dom (\<gamma>(a,b))) \<cong> T(a,b)" 
  by (metis M.A.Id_ex M.A.S1 M.AxA.Ex M.T.BiF.pres1 M.T.BiF.reflects_morp Sym.Braid.Br.\<eta>.presDom assms(1) assms(2) fst_conv snd_conv)

lemma Dom_simp[simp]: 
  assumes "M.A.IdEx a" and "M.A.IdEx b" 
  shows "(dom (\<gamma>(a,b))) = T(a,b)" 
  using Dom M.A.Id_ex2 assms(1) assms(2) by auto

lemma Cod: 
  assumes "M.A.Id a" and "M.A.Id b" 
  shows "(cod (\<gamma>(a,b))) \<cong> T(b,a)"
  by (metis M.A.Dom_I M.A.I_hom M.A.Id_ex M.A.S2 M.A.from_hom_set_def M.AxA.Ex M.T.BiF.pres2 M.T.BiF.reflects_morp Sym.Braid.Br.\<eta>.presCod assms(1) assms(2) fst_conv snd_conv)

lemma Cod_simp[simp]: 
  assumes "M.A.IdEx a" and "M.A.IdEx b" 
  shows "(cod (\<gamma>(a,b))) = T(b,a)"
  using Cod M.A.Id_ex2 assms(1) assms(2) by auto

lemma Inverses1[simp]: 
  assumes "M.A.IdEx a" and "M.A.IdEx b" 
  shows "\<gamma>(a,b)\<cdot>\<gamma>(b,a) \<simeq> T(b,a)" 
  by (smt Cod_simp Dom_simp M.A.Id_ex M.A.Id_ex2 M.A.S3 M.A.dom_of_comp M.A.invcheck2 M.AxA.Ex2 M.tensor_arrow_2 Sym.Braid.Br.\<eta>.ntExists Sym.Braid.Br.comp_iso Sym.Braid.Br_inv.identity_under_map Sym.symmetry assms(1) assms(2) fst_conv snd_conv)

end

end