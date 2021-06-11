theory Natural_Transformations
  imports Main Functors

begin

section \<open>Natural transformation\<close>

locale naturalTransformation =
A: category domain codomain composition nonex + 
B: category domain' codomain' composition' nonex' +
F: functorCat domain codomain composition nonex domain' codomain' composition' nonex' F + 
G: functorCat  domain codomain composition nonex domain' codomain' composition' nonex' G
for 
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex ::"'a" ("*") and
  domain'::"'b\<Rightarrow>'b" ("dom2 _") and
  codomain'::"'b\<Rightarrow>'b" ("cod2 _") and
  composition'::"'b\<Rightarrow>'b\<Rightarrow>'b" (infix "\<cdot>2" 110) and
  nonex' ::"'b" ("*2") and
  F :: "'a \<Rightarrow> 'b"  and
  G :: "'a \<Rightarrow> 'b"  +
fixes 
  \<eta> :: "'a \<Rightarrow> 'b"
assumes 
  ntExists: "(E x) \<longrightarrow> E(\<eta> x)" and
  nntExists: "\<not>(E x) \<longrightarrow> \<not>(E(\<eta> x))" and
  presDom: "(dom2 (\<eta> x)) \<cong> (dom2 (F x))" and
  presCod: "(cod2 (\<eta> x)) \<cong>  (cod2 (G x))" and
  naturality: "(E(z\<cdot>w)) \<longrightarrow> ((\<eta> z)\<cdot>2(F w)) \<simeq> ((G z)\<cdot>2(\<eta> w))"

begin 

lemma True 
   nitpick [satisfy, user_axioms, expect=genuine, card i=4-50] oops 

lemma ActOnMorph: 
  shows "\<eta> x \<cong> G (x)\<cdot>2(\<eta> (dom x))" 
  by (metis A.S5 B.Ex_two_ob1 B.Ex_two_ob2 B.S5 F.pres1 G.nexists naturality nntExists presDom)

lemma preserves_comp:
  assumes "E(z\<cdot>w)"
  shows "(\<eta>(z\<cdot>w)) \<^bold>\<ge> ((G z)\<cdot>2(\<eta> w))"
  by (smt A.S2 A.S3 A.S4 A.S5 B.S2 B.S3 B.S4 B.S5 F.pres1 G.exists G.pres3 assms naturality) 

lemma functor_equals_dom:
  assumes "functorCat domain codomain composition nonex domain' codomain' composition' nonex' \<eta>"
  shows "((F x) \<cong> (\<eta> x))"
  by (smt A.category_axioms B.category_axioms F.nexists assms category.S3 category.S6 functorCat.pres2 naturality nntExists ntExists preserves_comp)

lemma functor_equals_cod:
  assumes "functorCat domain codomain composition nonex domain' codomain' composition' nonex' \<eta>"
  shows "((G x) \<cong> (\<eta> x))"
  by (metis A.S5 B.S3 B.S5 F.pres1 G.nexists assms naturalTransformation.functor_equals_dom naturalTransformation_axioms nntExists ntExists preserves_comp)

lemma equalNT:
  assumes "naturalTransformation domain codomain composition nonex domain' codomain' composition' nonex' F G \<eta>" and 
          "naturalTransformation domain codomain composition nonex domain' codomain' composition' nonex' F G \<tau>" and
          "\<^bold>\<forall>x. A.Id x \<longrightarrow> ((\<eta> x) \<^bold>= (\<tau> x))"
  shows "(\<eta> y) \<cong> (\<tau> y)"
  by (smt A.Id_def A.S3 A.S5 A.S6 B.S3 B.S5 F.pres1 assms(2) assms(3) naturalTransformation_axioms naturalTransformation_axioms_def naturalTransformation_def)

end

lemma functors_is_nat_transformation:
  assumes "functorCat domain codomain composition nonex domain' codomain' composition' nonex' F"
  shows "naturalTransformation domain codomain composition nonex domain' codomain' composition' nonex' F F F"
  using assms
  apply unfold_locales
  apply (meson category.S1 functorCat.axioms(1))
  apply (meson category.S2 functorCat.axioms(1))
  apply (meson category.S3 functorCat.axioms(1))
  apply (meson category.S4 functorCat.axioms(1))
  apply (meson category.S5 functorCat.axioms(1))
  apply (meson category.S6 functorCat.axioms(1))
  apply (meson category.S1 functorCat.axioms(1))
  apply (meson category.SN functorCat.axioms(1))
  apply (meson category.S1 functorCat.axioms(2))
  apply (meson category.S2 functorCat.axioms(2))
  apply (meson category.S3 functorCat.axioms(2))
  apply (meson category.S4 functorCat.axioms(2))
  apply (meson category.S5 functorCat.axioms(2))
  apply (meson category.S6 functorCat.axioms(2)) 
  apply (meson category.SN functorCat.axioms(2))
  apply (simp add: functorCat.exists)
  apply (simp add: functorCat.nexists)
  apply (meson functorCat.pres1)
  apply (meson functorCat.pres2)
  apply (meson functorCat.pres3)
  apply auto[1]
  apply auto[1]
  by (meson functorCat.Pres3Equiv)

sublocale functorCat \<subseteq> naturalTransformation domain codomain composition nonex domain' codomain' composition' nonex' F F F
  by (simp add: functorCat_axioms functors_is_nat_transformation)

section \<open>Natural transformation via identities\<close>

locale naturalTransformationViaIdentities = 
A: category domain codomain composition nonex +
B: category domain' codomain' composition' nonex' +
F: functorCat domain codomain composition nonex domain' codomain' composition' nonex' F +
G: functorCat domain codomain composition nonex domain' codomain' composition' nonex' G 
for 
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex ::"'a" ("*") and
  domain'::"'b\<Rightarrow>'b" ("dom2 _") and
  codomain'::"'b\<Rightarrow>'b" ("cod2 _") and
  composition'::"'b\<Rightarrow>'b\<Rightarrow>'b" (infix "\<cdot>2" 110) and
  nonex' ::"'b" ("*2") and
  F :: "'a \<Rightarrow> 'b"  and
  G :: "'a \<Rightarrow> 'b"  +
fixes 
  \<eta> :: "'a \<Rightarrow> 'b" 
assumes 
  exists: "((dom a) \<simeq> a) \<longrightarrow> B.from_hom_set (\<eta> a) (F a) (G a)" and
  naturality: "(((G x)\<cdot>2(\<eta>(dom x))) \<cong> (\<eta>(cod x))\<cdot>2(F x))"
begin

definition map :: "'a \<Rightarrow> 'b" 
  where "map x = (if (E x) 
                 then (\<eta>(cod x))\<cdot>2(F x) 
                 else *2)"

lemma map_ide[simp]: 
  assumes "(dom a) \<simeq> a" 
  shows "map a \<simeq> \<eta> a" 
  by (smt A.cod_dom B.category_axioms assms category.S5 category.from_hom_set_def category.morph_hom exists local.map_def)

lemma components_transformation_4: 
  shows "(cod2 (map x)) \<cong>  (cod2 (G x))" 
  by (smt A.dom_cod B.S2 B.S3 B.S6 B.SN B.cod_of_comp B.from_hom_set_def F.pres2 G.nntExists G.ntExists G.pres2 exists local.map_def)

lemma components_transformation_5:
  shows "(E(z\<cdot>w)) \<longrightarrow> ((map z)\<cdot>2(F w)) \<simeq> ((G z)\<cdot>2(map w))" 
  by (smt A.Ex_two_ob1 A.Ex_two_ob2 A.S3 B.ExDomCod(1) B.S2 B.S3 B.S4 G.ntExists G.pres1 G.pres2 components_transformation_4 local.map_def naturality)

lemma components_transformation_3:
  shows "(dom2 (map x)) \<cong> (dom2 (F x))" 
  by (smt A.double_dom B.ExDomCod(2) B.SN B.category_axioms B.dom_of_comp B.from_hom_set_def F.nntExists F.pres1 G.pres1 category.S3 exists local.map_def naturality)

lemma def_nat_transformation: 
  shows "naturalTransformation domain codomain composition nonex domain' codomain' composition' nonex' F G map" 
  using map_def naturality
  apply (unfold_locales)
  apply (smt A.Ex_from_hom_set A.double_dom A.from_hom_set_def B.S3 B.category_axioms G.functorCat_axioms category.from_hom_set_def exists functorCat.pres1)
  apply (simp add: B.SN) 
  using components_transformation_3 apply blast
  using components_transformation_4 apply blast
  using components_transformation_5 by blast
end

sublocale naturalTransformationViaIdentities \<subseteq> naturalTransformation domain codomain composition nonex domain' codomain' composition' nonex' F G map
  by (simp add: def_nat_transformation)

section \<open>Natural isomorphism\<close>

locale naturalIsomorphism = 
A: category domain codomain composition nonex + 
B: category domain' codomain' composition' nonex' +
F: functorCat domain codomain composition nonex domain' codomain' composition' nonex' F + 
G: functorCat  domain codomain composition nonex domain' codomain' composition' nonex' G +
\<eta>: naturalTransformation domain codomain composition nonex domain' codomain' composition' nonex' F G \<eta>
for 
  domain :: "'a \<Rightarrow> 'a" ("dom _" [108] 109) and
  codomain :: "'a\<Rightarrow>'a" ("cod _" [110] 111) and
  composition :: "'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and 
  nonex :: "'a" ("*") and
  domain' :: "'b \<Rightarrow> 'b" ("dom2 _" [108] 109) and
  codomain' :: "'b\<Rightarrow>'b" ("cod2 _" [110] 111) and
  composition' :: "'b\<Rightarrow>'b\<Rightarrow>'b" (infix "\<cdot>2" 110) and
  nonex' :: "'b" ("*2") and
  F :: "'a \<Rightarrow> 'b" and
  G :: "'a \<Rightarrow> 'b" and
  \<eta> :: "'a \<Rightarrow> 'b" +
assumes 
  comp_iso: "A.IdEx x \<longrightarrow> (B.Iso (\<eta> x))"

begin 

lemma True 
  nitpick [satisfy, user_axioms, expect=genuine] oops

lemma pres_iso:
  assumes "A.Iso x"
  shows "B.Iso (\<eta> x)"
  by (smt A.IsoE A.double_dom A.inv_ex2 B.IsoComp F.functorCat_axioms G.iso_pres \<eta>.ActOnMorph \<eta>.ntExists assms category.S3 functorCat.axioms(1) local.comp_iso)

end

section \<open>Inverse natural transformation\<close>

locale inverse_natural_tr = 
A: category domain codomain composition nonex + 
B: category domain' codomain' composition' nonex' +
F: functorCat domain codomain composition nonex domain' codomain' composition' nonex' F + 
G: functorCat  domain codomain composition nonex domain' codomain' composition' nonex' G +
\<eta>: naturalIsomorphism domain codomain composition nonex domain' codomain' composition' nonex' F G \<eta>
for 
  domain :: "'a \<Rightarrow> 'a" ("dom _" [108] 109) and
  codomain :: "'a\<Rightarrow>'a" ("cod _" [110] 111) and
  composition :: "'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and 
  nonex :: "'a" ("*") and
  domain' :: "'b \<Rightarrow> 'b" ("dom2 _" [108] 109) and
  codomain' :: "'b\<Rightarrow>'b" ("cod2 _" [110] 111) and
  composition' :: "'b\<Rightarrow>'b\<Rightarrow>'b" (infix "\<cdot>2" 110) and
  nonex' :: "'b" ("*2") and
  F :: "'a \<Rightarrow> 'b" and
  G :: "'a \<Rightarrow> 'b" and
  \<eta> :: "'a \<Rightarrow> 'b" 

begin 

lemma True 
  nitpick [satisfy, user_axioms, expect=genuine] oops

lemma int1: 
  shows "((dom a) \<simeq> a) \<Longrightarrow> B.from_hom_set (B.inv (\<eta> a)) (G a) (F a)"
proof -
  assume a1: "((dom a) \<simeq> a)"
  have a2: "(B.Iso (\<eta> a))" 
    using \<eta>.comp_iso a1 by blast
  have a3: "E(B.inv (\<eta> a))" 
    using B.Ex_two_ob1 B.inv_ex a2 by blast
  have a4: "B.from_hom_set (\<eta> a) (F a) (G a)" 
    by (metis A.cod_dom B.from_hom_set_def F.ntExists F.pres1 G.ntExists G.pres2 \<eta>.\<eta>.presCod \<eta>.\<eta>.presDom a1)
  have a5: "E (F a)" 
    using F.ntExists a1 by blast
  have a6: "E (G a)" 
    using G.ntExists a1 by blast
  have a7: "(dom2 (B.inv (\<eta> a))) = (G a)" 
    by (metis B.S3 B.from_hom_set_def B.inv_ex a2 a4)
  have a8: "cod a \<simeq> a" 
    using A.cod_dom a1 by fastforce
  have a9: "E(cod a) \<and> E a \<and> (cod a \<^bold>= a)" 
    using a8 by blast
  have a10: "(cod2 (B.inv (\<eta> a))) = (F a)" 
    using B.Iso_inv_cod a2 a4 by blast
  have a11: "B.from_hom_set (B.inv (\<eta> a)) (G a) (F a)" 
    by (simp add: B.Iso_inv_hom a2 a4)
  show ?thesis 
    using a11 by blast
qed

lemma int2:
  shows "((dom a) \<simeq> a) \<^bold>\<rightarrow> B.from_hom_set (B.inv (\<eta> a)) (G a) (F a)" 
  using int1 by blast

lemma int3: 
  assumes "(((G x)\<cdot>2(\<eta>(dom x))) \<cong> (\<eta>(cod x))\<cdot>2(F x))" 
  shows "(E x) \<longrightarrow> (((G x)\<cdot>2(\<eta>(dom x))) \<cong> (\<eta>(cod x))\<cdot>2(F x))" 
  using assms by auto

lemma int4: 
  assumes "(E x) \<longrightarrow> (((G x)\<cdot>2(\<eta>(dom x))) \<cong> (\<eta>(cod x))\<cdot>2(F x))"
  shows "(((G x)\<cdot>2(\<eta>(dom x))) \<cong> (\<eta>(cod x))\<cdot>2(F x))" 
  using B.Ex_two_ob1 B.Ex_two_ob2 F.reflects_morp G.reflects_morp assms by blast

interpretation \<eta>': naturalTransformationViaIdentities domain codomain composition nonex domain' codomain' composition' nonex' G F "\<lambda>a. B.inv (\<eta> a)"
  apply (unfold_locales, simp_all)
  apply (simp add: int2)  
  using int4 int3 
  by (smt A.category_axioms A.dom_cod B.Ex_from_hom_set B.Id_cod B.Id_def B.Iso_def B.S5 B.S6 B.category_axioms B.cod_of_comp B.commSquare1 B.dom_of_comp B.from_hom_set_def F.functorCat_axioms F.reflects_morp G.pres2 \<eta>.\<eta>.naturality \<eta>.\<eta>.ntExists \<eta>.\<eta>.presCod \<eta>.\<eta>.presDom \<eta>.comp_iso category.S3 category.arrow_and_inv1 category.cod_dom functorCat.pres1 functorCat.pres2 int1)

definition map 
  where "map = \<eta>'.map" 

lemma identity_under_map[simp]: 
  assumes "dom a \<simeq> a" 
  shows "map a = B.inv (\<eta> a)" 
  using \<eta>'.map_ide assms local.map_def by auto

lemma arrows_under_map[simp]: 
  assumes "E (x::'a)"
  shows "map x = (B.inv (\<eta> (cod x)))\<cdot>2(G x)" 
  by (simp add: \<eta>'.map_def assms local.map_def)

lemma inverse_components: 
  assumes "dom a \<simeq> a" 
  shows "B.inv_arrows (\<eta> a) (map a)" 
  by (smt A.cod_dom B.Id_def B.Iso_hom_set B.Iso_inv_cod B.S3 B.S4 B.S5 B.category_axioms \<eta>'.naturality \<eta>.\<eta>.naturalTransformation_axioms \<eta>.\<eta>.ntExists \<eta>.naturalIsomorphism_axioms assms category.Iso_def category.arrow_and_inv1 category.inv_arrows_def identity_under_map naturalIsomorphism.comp_iso naturalTransformation.presCod)

lemma inverse_is_nat_transformation: 
  shows "naturalIsomorphism domain codomain composition nonex domain' codomain' composition' nonex' G F map" 
   by (smt A.S5 A.category_axioms B.Id3 B.Id_ex B.Iso_hom_set B.Iso_inv_cod B.S4 B.arrow_and_inv1 B.category_axioms B.cod_of_comp F.functorCat_axioms G.functorCat_axioms \<eta>'.map_def \<eta>'.naturalTransformation_axioms \<eta>.\<eta>.naturalTransformation_axioms \<eta>.\<eta>.naturality \<eta>.naturalIsomorphism_axioms category.Iso_def category.S3 functorCat.pres1 local.map_def naturalIsomorphism.comp_iso naturalIsomorphism.intro naturalIsomorphism_axioms.intro naturalTransformation.ntExists naturalTransformation.preserves_comp)

end

sublocale inverse_natural_tr \<subseteq> naturalTransformation domain codomain composition nonex domain' codomain' composition' nonex' G F map 
  using inverse_is_nat_transformation naturalIsomorphism_def 
  by (simp add: naturalIsomorphism_def)

sublocale inverse_natural_tr \<subseteq> naturalIsomorphism domain codomain composition nonex domain' codomain' composition' nonex' G F map
  by (simp add: inverse_is_nat_transformation)

sublocale functorCat \<subseteq> naturalIsomorphism domain codomain composition nonex domain' codomain' composition' nonex' F F F
  apply unfold_locales
  using pres_identity B.ide_is_iso
  by (simp add: A.Id_def ntExists)

lemma nat_transform_impl_inverse: 
  assumes "naturalIsomorphism domain codomain composition nonex domain' codomain' composition' nonex' F G \<eta>" 
  shows "inverse_natural_tr domain codomain composition nonex domain' codomain' composition' nonex' F G \<eta>" 
  using assms inverse_natural_tr_def naturalIsomorphism_def 
  by (simp add: inverse_natural_tr_def naturalIsomorphism_def)

section \<open>Binary functor defines natural transformations\<close>

context biFunctor

begin

lemma fix_arr1n:
  assumes "E x1" 
  shows "naturalTransformation domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' (\<lambda>x2. BF (domain x1, x2)) (\<lambda>x2. BF (codomain x1, x2)) (\<lambda>x2. BF (x1,x2))"
  using assms
  apply unfold_locales
  using A.from_hom_set_def AxB.Ex ntExists 
  using A.Ex_from_hom_set apply blast
  using AxB.Ex nntExists apply blast
  apply (metis A.double_dom AxB.Ex fst_conv nntExists pres1 snd_conv)
  apply (metis A.S3 A.S5 fst_conv pres2 snd_conv)
  using A.S5 A.double_dom A.from_hom_set_def fst_conv pres3 snd_conv 
  apply (metis AxB.Ex nntExists)
  using A.from_hom_set_def AxB.Ex ntExists 
  apply (meson A.Ex_from_hom_set)
  using AxB.Ex nntExists apply blast
  apply (metis A.S3 A.S6 fst_conv pres1 snd_conv)
  apply (metis A.double_cod AxB.Ex fst_conv nntExists pres2 snd_conv)
  apply (metis A.S6 A.double_cod AxB.Ex fst_conv nntExists pres3 snd_conv)
  using A.morph_hom AxB.Ex ntExists apply blast  
  using AxB.Ex nntExists apply blast
  apply (metis (no_types, lifting) A.Ex_from_hom_set A.double_dom A.from_hom_set_def fst_conv pres1 snd_conv)
  apply (smt A.Ex_from_hom_set A.double_cod A.from_hom_set_def fst_conv pres2 snd_conv)
  by (metis A.S5 A.S6 AxB.Ex fst_conv ntExists pres3 snd_conv)

lemma fix_arr2:
  assumes "E x2" 
  shows "naturalTransformation domain codomain composition nonex domain'' codomain'' composition'' nonex'' (\<lambda>x1. BF (x1, dom2 x2)) (\<lambda>x1. BF (x1, cod2 x2)) (\<lambda>x1. BF (x1,x2))"
  using assms
  apply unfold_locales
  using A.from_hom_set_def AxB.Ex ntExists 
  using B.Ex_from_hom_set 
  apply (meson B.from_hom_set_def)
  using AxB.Ex nntExists apply blast
  apply (metis AxB.Ex B.double_dom fst_conv nntExists pres1 snd_conv)
  apply (metis B.S3 B.S5 fst_conv pres2 snd_conv)
  using A.S5 A.double_dom A.from_hom_set_def fst_conv pres3 snd_conv 
  using A.from_hom_set_def AxB.Ex ntExists 
  using AxB.Ex nntExists 
  apply (metis B.S6 B.cod_dom)
  using AxB.Ex B.Ex_from_hom_set B.from_hom_set_def ntExists apply blast
  apply (metis AxB.Ex nntExists)
  apply (metis AxB.Ex B.dom_cod fst_conv nntExists pres1 snd_conv)
  using A.morph_hom AxB.Ex ntExists 
  apply (metis B.double_cod fst_conv nntExists pres2 snd_conv)  
  apply (metis AxB.Ex B.S5 B.dom_cod fst_conv pres3 reflects_morp snd_conv)
  using AxB.Ex ntExists apply blast
  using AxB.Ex reflects_morp apply blast
  apply (metis AxB.Ex B.double_dom fst_conv nntExists pres1 snd_conv)
  apply (metis B.S3 B.S6 B.double_cod fst_conv pres2 snd_conv)
  by (smt AxB.Ex B.S5 B.category_axioms category.S6 fst_conv ntExists pres3 snd_conv)

lemma fix_arr1:
  assumes "E x1" 
  shows "naturalTransformationViaIdentities domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' (\<lambda>x2. BF (domain x1, x2)) (\<lambda>x2. BF (codomain x1, x2)) (\<lambda>x2. BF (x1,x2))"
  using assms
  apply unfold_locales
  apply (metis A.S3 A.S5 AxB.Ex ntExists)
  using AxB.Ex reflects_morp apply blast
  apply (metis A.double_dom AxB.Ex fst_conv nntExists pres1 snd_conv)
  apply (metis A.S3 A.S5 fst_conv pres2 snd_conv)
  apply (metis A.S5 A.double_dom AxB.Ex fst_conv preserves_comp reflects_morp snd_conv)
  apply (metis A.Ex_two_ob1 A.S6 AxB.Ex ntExists)
  using AxB.Ex reflects_morp apply blast
  apply (metis A.S3 A.S6 fst_conv pres1 snd_conv)
  apply (metis A.Ex_two_ob1 A.S6 A.double_cod fst_conv pres2 snd_conv)
  apply (metis A.S6 A.double_cod AxB.Ex Pres3Equiv fst_conv nntExists snd_conv)
  apply (smt A.S5 ActOnMorph AxB.Ex C.ExDomCod(1) C.from_hom_set_def biFunctor_axioms biFunctor_def category.S3 category.cod_dom fst_conv ntExists pres2 snd_conv)
  by (smt A.S5 AxB.Ex AxB.prod_S6 B.cod_dom C.Ex_two_ob2 C.S5 Pres3Equiv biFunctor_axioms biFunctor_def category.S3 fst_conv nntExists pres1 snd_conv)

lemma fix_arr2n:
  assumes "E x2" 
  shows "naturalTransformationViaIdentities domain codomain composition nonex domain'' codomain'' composition'' nonex'' (\<lambda>x1. BF (x1, dom2 x2)) (\<lambda>x1. BF (x1, cod2 x2)) (\<lambda>x1. BF (x1,x2))"
  using assms
  apply unfold_locales
  apply (metis AxB.Ex B.S3 B.S5 ntExists)
  using AxB.Ex reflects_morp apply blast
  apply (metis B.double_dom AxB.Ex fst_conv nntExists pres1 snd_conv)
  apply (metis B.S3 B.S5 fst_conv pres2 snd_conv)
  apply (metis B.S5 B.double_dom AxB.Ex fst_conv preserves_comp reflects_morp snd_conv)
  apply (metis B.Ex_two_ob1 B.S6 AxB.Ex ntExists)
  using AxB.Ex reflects_morp apply blast
  apply (metis B.S3 B.S6 fst_conv pres1 snd_conv)
  apply (metis B.Ex_two_ob1 B.S6 B.double_cod fst_conv pres2 snd_conv)
  apply (metis B.S6 B.double_cod AxB.Ex Pres3Equiv fst_conv nntExists snd_conv)
  apply (smt B.S5 ActOnMorph AxB.Ex C.ExDomCod(1) C.from_hom_set_def biFunctor_axioms biFunctor_def category.S3 category.cod_dom fst_conv ntExists pres2 snd_conv)
  by (smt B.S5 AxB.Ex AxB.prod_S6 A.cod_dom C.Ex_two_ob2 C.S5 Pres3Equiv biFunctor_axioms biFunctor_def category.S3 fst_conv nntExists pres1 snd_conv)

end

end