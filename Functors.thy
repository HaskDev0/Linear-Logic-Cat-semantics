theory Functors
  imports Main Categories

begin

section \<open>Functor\<close>

locale functorCat =
A: category domain codomain composition nonex + 
B: category domain' codomain' composition' nonex'
for 
  domain :: "'a \<Rightarrow> 'a" ("dom _") and
  codomain :: "'a \<Rightarrow> 'a" ("cod _") and
  composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  domain' ("dom2 _") and
  codomain' ("cod2 _")  and
  composition' (infix "\<cdot>2" 110) and
  nonex' :: "'b" ("*2") +
fixes 
  F :: "'a \<Rightarrow> 'b"
assumes 
  exists: "(E x) \<longrightarrow> E(F x)" and
  nexists:"(\<not>(E x)) \<longrightarrow> (\<not>(E(F x)))" and
  pres1: "(F (dom x)) \<cong> dom2 (F x)" and
  pres2: "(F (cod x)) \<cong> cod2 (F x)" and
  pres3: "(F (x\<cdot>y)) \<^bold>\<ge> (F x)\<cdot>2(F y)" 

begin  
  lemma True 
    nitpick [satisfy, user_axioms, format= 2, expect=genuine, card 'a = 2-10] oops 

lemma Pres3Equiv: 
  shows "E(x\<cdot>y) \<longrightarrow> (F (x\<cdot>y)) \<simeq> (F x)\<cdot>2(F y)" 
  using exists pres3 by auto

lemma reflects_morp:
  shows "(E(F x)) \<longrightarrow> (E x)"
  using nexists by blast

lemma pres_identity:
  assumes "1\<^sub>x"
  shows "B.Id (F x)"
  by (metis A.Id_def B.Id_def assms nexists pres1)

lemma iso_pres:
  assumes "A.Iso x"
  shows "B.Iso (F x)"
  by (smt A.Id_def A.S3 A.S4 A.S5 A.category_axioms B.Iso_def assms category.Iso_def category.S2 exists pres3 pres_identity)

lemma linv_pres:
  assumes "A.leftinv x" 
  shows "B.leftinv (F x)"
  by (metis A.leftinv_def B.leftinv_def assms exists pres3 pres_identity) 

lemma rinv_pres:
  assumes "A.rightinv x" 
  shows "B.rightinv (F x)"
  by (metis A.rightinv_def B.rightinv_def assms exists pres3 pres_identity)

end

section \<open>Composition functor\<close>

lemma comp_functor:
  assumes "functorCat domain codomain composition nonex domain' codomain' composition' nonex' F" and
          "functorCat domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' G"
  shows "functorCat domain codomain composition nonex domain'' codomain'' composition'' nonex'' (G o F)"
  by (smt assms(1) assms(2) comp_apply functorCat.axioms(1) functorCat.axioms(2) functorCat.axioms(3) functorCat.intro functorCat.pres3 functorCat_axioms_def)

locale comp_functor = 
F: functorCat domain codomain composition nonex domain' codomain' composition' nonex' F +
G: functorCat domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' G
for 
  domain :: "'a \<Rightarrow> 'a" ("dom _") and
  codomain :: "'a \<Rightarrow> 'a" ("cod _") and
  composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  domain' :: "'b \<Rightarrow> 'b" ("dom2 _") and
  codomain' :: "'b \<Rightarrow> 'b" ("cod2 _") and
  composition' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infix "\<cdot>2" 110) and
  nonex' :: "'b" ("*2") and
  domain'' :: "'c \<Rightarrow> 'c" ("dom3 _") and
  codomain'' :: "'c \<Rightarrow> 'c" ("cod3 _") and
  composition'' :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" (infix "\<cdot>3" 110) and
  nonex'' :: "'c" ("*3") and
  F :: "'a \<Rightarrow> 'b" and 
  G :: "'b \<Rightarrow> 'c"
begin
    abbreviation map
      where "map \<equiv> G o F"
end

sublocale comp_functor \<subseteq> functorCat domain codomain composition nonex domain'' codomain'' composition'' nonex'' map
  using F.functorCat_axioms G.functorCat_axioms comp_functor by fastforce

section \<open>Endofunctor\<close>

locale endofunctor = 
functorCat domain codomain composition nonex domain codomain composition nonex F
for 
  domain :: "'a \<Rightarrow> 'a" ("dom _") and
  codomain :: "'a \<Rightarrow> 'a" ("cod _") and
  composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  F ::"'a \<Rightarrow> 'a"

section \<open>Faithful functor\<close>

locale faithfulfunctor = 
A: category domain codomain composition nonex +
B: category domain' codomain' composition' nonex' +
functorCat domain codomain composition nonex domain' codomain' composition' nonex' F
for 
  domain :: "'a \<Rightarrow> 'a" ("dom _") and
  codomain :: "'a \<Rightarrow> 'a" ("cod _") and
  composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  domain' :: "'b \<Rightarrow> 'b" ("dom2 _") and
  codomain' :: "'b \<Rightarrow> 'b" ("cod2 _") and
  composition' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infix "\<cdot>2" 110) and
  nonex' :: "'b" ("*2") and
  F :: "'a \<Rightarrow> 'b" +
assumes 
  faith:"((A.par x y) \<and> (F x \<simeq> F y)) \<longrightarrow> (x \<simeq> y)"

begin  
  lemma True 
    nitpick [satisfy, user_axioms, format= 2, expect=genuine, card 'a = 4 -10] oops 

lemma refl_ide:
  assumes "A.from_hom_set x a a" and "B.Id (F x)"
  shows "A.Id x"
  using assms faith
proof -
  have 1: "A.from_hom_set x a a"
    using assms(1) by blast
  have 2: "A.from_hom_set a a a" 
    using "1" A.Id_from_hom_set A.Id_hom A.from_hom_set_def by blast
  have 3: "B.Id (F x)" 
    by (simp add: assms(2))
  have 4: "B.Id (F a)" 
    using "2" A.Id_def A.from_hom_set_def pres_identity by blast
  have 5: "A.par x a"
    using "1" "2" A.from_hom_set_def by auto
  have 6: "(F x) \<simeq> (F a)"
    by (metis "3" "4" "5" B.Id_def exists pres1)
  have 7: "((A.par x a) \<and> (F x \<simeq> F a))"
    using "5" "6" by blast
  have 8: "(x \<simeq> a)" using faith[where x = \<open>x\<close> and y = \<open>a\<close>] 
    using "5" "6" by blast
  show ?thesis 
    using "2" "8" A.Id_from_hom_set by blast
qed

lemma comp_help: "((A.par (x::'a) (y::'a)) \<and> (F x \<simeq> F y)) \<Longrightarrow> (x \<simeq> y)" 
   using faith by blast

lemma comp_faith_func:
  assumes "faithfulfunctor domain codomain composition nonex domain' codomain' composition' nonex' F" and
          "faithfulfunctor domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' G"
  shows "comp_functor domain codomain composition nonex domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' F G" 
  by (meson assms(1) assms(2) comp_functor.intro faithfulfunctor_def)

end 

lemma comp_faith:
  assumes "faithfulfunctor domain codomain composition nonex domain' codomain' composition' nonex' F" and
          "faithfulfunctor domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' G"
  shows "faithfulfunctor domain codomain composition nonex domain'' codomain'' composition'' nonex'' (G o F)"
proof-
  interpret F: faithfulfunctor domain codomain composition nonex domain' codomain' composition' nonex' F 
    by (simp add: assms(1))
  interpret G: faithfulfunctor domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' G
    by (simp add: assms(2))
  interpret A: category domain codomain composition nonex
    by (simp add: F.A.category_axioms)
  interpret B: category domain' codomain' composition' nonex'
    by (simp add: F.B.category_axioms)
  interpret C: category domain'' codomain'' composition'' nonex''
    by (simp add: G.B.category_axioms)
  have 0: "faithfulfunctor domain codomain composition nonex domain' codomain' composition' nonex' F" and
"faithfulfunctor domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' G" 
    using F.faithfulfunctor_axioms apply simp 
    using G.faithfulfunctor_axioms by blast
  from 0 have 1: "comp_functor domain codomain composition nonex domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' F G" 
    by (simp add: assms(2) faithfulfunctor.comp_faith_func)
  from 1 have 2: "functorCat domain codomain composition nonex domain'' codomain'' composition'' nonex'' (G o F)"
    by (meson comp_functor comp_functor_def)
  have 3: "(F.A.par x y) \<^bold>\<and> ((G o F) x \<simeq> (G o F) y) \<Longrightarrow> (x \<simeq> y)" for x y
  proof -
    assume 0: "(F.A.par x y) \<^bold>\<and> ((G o F) x \<simeq> (G o F) y)"
    from 0 have 1: "(F.A.par x y)" by linarith
    from 1 have 2: "F.B.par (F x) (F y)"  by (metis F.exists F.pres1 F.pres2)
     have 3: "((G o F) x \<simeq> (G o F) y)" using "0" by blast
     from 2 and 3 have 4: "(F.B.par (F x) (F y)) \<^bold>\<and> ((G o F) x \<simeq> (G o F) y)" 
       by blast
     from 4 have 5: "(F.B.par ((F x)::'b) ((F y)::'b)) \<^bold>\<and> (G(F x) \<simeq> G(F y))" 
       by simp
     thm G.faith
     thm F.faith
     from 5 have 6: "(F x) \<simeq> (F y)" using G.faith[where x = \<open>F x\<close> and y = \<open>F y\<close>]
       by blast
     from 1 and 6 have 7: "(F.A.par x y) \<^bold>\<and> (F x) \<simeq> (F y)" using F.faith 
       by blast
     from 7 have 8: "(x \<simeq> y)" using F.comp_help F.faith[where x = \<open>x\<close> and y = \<open>y\<close>]
       by blast
     show ?thesis using 8 by auto
   qed
     have 9:  "((F.A.par x y) \<^bold>\<and> ((G o F) x \<simeq> (G o F) y)) \<^bold>\<rightarrow> (x \<simeq> y)" for x y using 3[where x = \<open>x\<close> and y = \<open>y\<close>]  
     by blast
   have "faithfulfunctor domain codomain composition nonex domain'' codomain'' composition'' nonex'' (G \<circ> F)" using 2 9
     by (smt F.A.category_axioms G.B.category_axioms faithfulfunctor.intro faithfulfunctor_axioms.intro)
   thus ?thesis by blast
 qed

section \<open>Identity functor\<close>

locale identityfunc = 
A: category 
begin 

definition map :: "'a \<Rightarrow> 'a"
  where "map x = x"

  lemma isfunctor:
    shows "functorCat domain codomain composition nonex domain codomain composition nonex map"
     by (simp add: A.category_axioms functorCat.intro functorCat_axioms_def local.map_def)
end

sublocale identityfunc \<subseteq> functorCat domain codomain composition nonex domain codomain composition nonex map
  using isfunctor by auto

sublocale category \<subseteq> identityfunc domain codomain composition nonex 
  by (simp add: category_axioms identityfunc.intro)

section \<open>Binary functor\<close>

locale biFunctor = 
A: category domain codomain composition nonex +
B: category domain' codomain' composition' nonex' +
AxB: productCategory domain codomain composition nonex domain' codomain' composition' nonex' +
C: category domain'' codomain'' composition'' nonex'' +
functorCat AxB.Dom AxB.Cod AxB.Composition AxB.Nonex domain'' codomain'' composition'' nonex'' BF
for 
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex ::"'a" ("*") and
  domain'::"'b\<Rightarrow>'b" ("dom2 _") and
  codomain'::"'b\<Rightarrow>'b" ("cod2 _") and
  composition'::"'b\<Rightarrow>'b\<Rightarrow>'b" (infix "\<cdot>2" 110) and
  nonex' ::"'b" ("2") and
  domain''::"'c\<Rightarrow>'c" ("dom3 _") and
  codomain''::"'c\<Rightarrow>'c" ("cod3 _") and
  composition''::"'c\<Rightarrow>'c\<Rightarrow>'c" (infix "\<cdot>3" 110) and
  nonex'' ::"'c" ("*3") and
  BF :: "'a * 'b \<Rightarrow> 'c"

begin 

 lemma True 
   nitpick [satisfy, user_axioms, expect=genuine, card 'a=2,card 'b=4,card 'c=8] oops 

lemma fix_arg1:
  assumes "A.Id a \<^bold>\<and> E a "
  shows "functorCat domain' codomain' composition' nonex' domain'' codomain'' composition'' nonex'' (\<lambda>x2. BF (a, x2))"
  using assms
  apply unfold_locales
  using AxB.Ex exists apply blast
  using AxB.Ex nexists apply blast
  apply (metis A.Id_def fst_conv pres1 snd_conv)  
  apply (metis A.Id3 fst_conv pres2 snd_conv)  
  by (smt A.Id3 A.category_axioms category.S6 fst_conv pres3 snd_conv)

lemma fix_arg2:
  assumes "B.Id a \<^bold>\<and> E a"
  shows "functorCat domain codomain composition nonex domain'' codomain'' composition'' nonex'' (\<lambda>x1. BF (x1, a))"
  using assms
  apply unfold_locales
  using AxB.Ex exists apply blast
  using AxB.Ex nexists apply blast
  apply (metis B.Id_def fst_conv pres1 snd_conv)
  apply (metis B.Id3 fst_conv pres2 snd_conv)  
  by (metis B.Id3 B.category_axioms category.S6 fst_conv pres3 snd_conv)

subsection \<open>Exchange binary functor\<close>

abbreviation Exch 
  where "Exch \<equiv> (\<lambda>x. BF(snd x, fst x))" 

lemma Exch_is_binary: 
  shows "biFunctor domain' codomain' composition' nonex' domain codomain composition nonex domain'' codomain'' composition'' nonex'' Exch" 
  apply unfold_locales
  using AxB.Ex2 apply blast
  using AxB.Ex apply blast
  apply (metis A.S1 AxB.Ex2 B.S1 prod.exhaust_sel)
  apply (metis A.S2 AxB.Ex2 B.S2 prod.exhaust_sel)
  apply (metis A.S3 AxB.Ex2 B.S3 old.prod.inject)
  apply (metis A.S4 AxB.Ex2 B.S4 fst_conv snd_conv)
  apply (metis A.S5 AxB.Ex2 B.S5 eq_fst_iff sndI)
  apply (metis A.S6 AxB.Ex2 B.S6 eq_fst_iff eq_snd_iff)
  using A.SN AxB.Ex2 apply blast
  using AxB.Ex AxB.Ex2 apply auto[1]
  using AxB.Ex AxB.Ex2 apply auto[1]
  using pres1 apply auto[1]
  using pres2 apply auto[1]
  using pres3  AxB.SN  exists apply blast
  using AxB.Ex AxB.Ex2 apply auto[1]
  using AxB.Ex AxB.Ex2 apply auto[1] 
  using pres1 apply auto[1] 
  using pres2 apply auto[1] 
  using pres3  nexists apply blast
  using pres1 apply auto[1]
  using pres2 apply auto[1]
  using pres3 by auto[1]

lemma Exch_simp[simp]: 
  shows "Exch (x,y) \<cong> BF (y,x)" 
  by simp

end

section \<open>Product functor\<close>

locale prodFunctor = 
A: category domain codomain composition nonex +
B: category domain' codomain' composition' nonex' +
C: category domain'' codomain'' composition'' nonex'' +
D: category domain''' codomain''' composition''' nonex''' +
F: functorCat domain codomain composition nonex domain'' codomain'' composition'' nonex'' F +
G: functorCat domain' codomain' composition' nonex' domain''' codomain''' composition''' nonex''' G +
AB: productCategory domain codomain composition nonex domain' codomain' composition' nonex' +
CD: productCategory domain'' codomain'' composition'' nonex'' domain''' codomain''' composition''' nonex'''
for 
  domain::"'a\<Rightarrow>'a" ("dom _") and
  codomain::"'a\<Rightarrow>'a" ("cod _") and
  composition::"'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110) and
  nonex ::"'a" ("*") and
  domain'::"'b\<Rightarrow>'b" ("dom2 _") and
  codomain'::"'b\<Rightarrow>'b" ("cod2 _") and
  composition'::"'b\<Rightarrow>'b\<Rightarrow>'b" (infix "\<cdot>2" 110) and
  nonex' ::"'b" ("*2") and
  domain''::"'c\<Rightarrow>'c" ("dom3 _") and
  codomain''::"'c\<Rightarrow>'c" ("cod3 _") and
  composition''::"'c\<Rightarrow>'c\<Rightarrow>'c" (infix "\<cdot>3" 110) and
  nonex'' ::"'c" ("*3") and
  domain'''::"'d\<Rightarrow>'d" ("dom4 _") and
  codomain'''::"'d\<Rightarrow>'d" ("cod4 _") and
  composition'''::"'d\<Rightarrow>'d\<Rightarrow>'d" (infix "\<cdot>4" 110) and
  nonex''' ::"'d" ("*4") and
  F::"'a\<Rightarrow>'c" and
  G::"'b\<Rightarrow>'d"
begin 

definition map::"'a*'b \<Rightarrow> 'c*'d"
  where "map f = (F (fst f), G (snd f))"

lemma is_functor:
  shows "functorCat AB.Dom AB.Cod AB.Composition AB.Nonex CD.Dom CD.Cod CD.Composition CD.Nonex map"
  apply (unfold_locales)
  using AB.Ex CD.Ex G.exists local.map_def 
  apply auto[1]
  using F.exists 
  apply blast
  apply (metis AB.Ex CD.Ex F.reflects_morp G.reflects_morp local.map_def prod.exhaust_sel)
  using CD.Ex F.pres1 G.pres1 local.map_def 
  apply auto[1]
  using CD.Ex F.pres2 G.pres2 local.map_def 
  apply auto[1]
  using CD.Ex F.pres3 G.pres3 local.map_def 
  by fastforce 

end

sublocale prodFunctor \<subseteq> functorCat AB.Dom AB.Cod AB.Composition AB.Nonex CD.Dom CD.Cod CD.Composition CD.Nonex map
  using is_functor by auto

end