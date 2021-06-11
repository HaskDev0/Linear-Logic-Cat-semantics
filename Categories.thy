theory Categories
  imports Main PositiveFreeHOL

begin

section \<open>Equalities\<close>

abbreviation KlEq (infixr "\<cong>" 56)  \<comment> \<open>Kleene equality\<close>
 where "x \<cong> y \<equiv> (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<^bold>= y"  

abbreviation ExId (infixr "\<simeq>" 56)  \<comment> \<open>Existing identity\<close> 
  where "x \<simeq> y \<equiv> E x \<^bold>\<and> E y \<^bold>\<and> x \<^bold>= y"

abbreviation dirEq (infixr "\<^bold>\<ge>" 56)  \<comment> \<open>Directed euality\<close>
  where "x \<^bold>\<ge> y \<equiv> E x \<^bold>\<rightarrow> (x = y)"

lemma "x \<cong> x \<^bold>\<and> (x \<cong> y \<^bold>\<rightarrow> y \<cong> x) \<^bold>\<and> ((x \<cong> y \<^bold>\<and> y \<cong> z) \<^bold>\<rightarrow> x \<cong> z)" by blast
lemma "x \<simeq> x" nitpick [user_axioms, show_all, format = 2, expect = genuine] oops  
lemma " (x \<simeq> y \<^bold>\<rightarrow> y \<simeq> x) \<^bold>\<and> ((x \<simeq> y \<^bold>\<and> y \<simeq> z) \<^bold>\<rightarrow> x \<simeq> z)" by blast
lemma "x \<simeq> y \<^bold>\<rightarrow> x \<cong> y" by simp
lemma "x \<simeq> y \<^bold>\<leftarrow> x \<cong> y" nitpick [user_axioms, show_all, format = 2, expect = genuine] oops

lemma "x \<^bold>\<ge> x" 
  by simp

section \<open>Additional facts to simplify the proofs\<close>

lemma THE_to_I: 
  assumes "y = (THE x. \<phi>(x))" and "E y" and "\<exists>! x. \<phi>(x)"
  shows "y = (\<^bold>I x. \<phi>(x))" 
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) theI_unique)

lemma I_to_THE1: 
  assumes "y = (\<^bold>I x. \<phi>(x))" and "\<^bold>\<exists>! x. \<phi>(x)" 
  shows "E y" 
  by (metis (mono_tags, lifting) assms(1) assms(2) theI')

lemma I_to_THE2: 
  assumes "y = (\<^bold>I x. \<phi>(x))" and "\<exists>! x. (\<phi>(x) \<and> (E x))"
  shows "y = (THE x. \<phi>(x))" oops

lemma Free_Impl: 
  assumes "A \<Longrightarrow> B" 
  shows "A \<longrightarrow> B" 
  using assms by blast

lemma Free_Impl2: 
  assumes "A \<longrightarrow> B" 
  shows "A \<Longrightarrow> B" 
  using assms by blast

lemma Free_And: 
  assumes "A \<and> B" 
  shows "A \<^bold>\<and> B" 
  using assms by blast

lemma Free_Or: 
  assumes "A \<or> B" 
  shows "A \<^bold>\<or> B" 
  using assms by blast

lemma Free_Equiv: 
  assumes "A \<longleftrightarrow> B" 
  shows "A \<^bold>\<leftrightarrow> B" 
  using assms by blast

lemma Free_Not: 
  assumes "\<not>A" 
  shows "\<^bold>\<not>A" 
  using assms by blast

lemma Free_And2[simp]: 
  assumes "A \<^bold>\<and> B" 
  shows "A \<and> B" 
  using assms by blast

lemma Free_Or2[simp]: 
  assumes "A \<^bold>\<or> B" 
  shows "A \<or> B" 
  using assms by blast

lemma Free_Equiv2[simp]: 
  assumes "A \<^bold>\<leftrightarrow> B" 
  shows "A \<longleftrightarrow> B" 
  using assms by blast

lemma Free_Not2[simp]: 
  assumes "\<^bold>\<not>A" 
  shows "\<not>A" 
  using assms by blast

sledgehammer_params [provers = cvc4 z3 e vampire spass remote_leo3, timeout = 300, isar_proofs = false]

section \<open>Category\<close>

locale category =
fixes 
  domain :: "'a \<Rightarrow> 'a" ("dom _" [108] 109) and
  codomain :: "'a \<Rightarrow> 'a" ("cod _" [110] 111) and
  composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<cdot>" 110) and 
  nonex :: "'a" ("*") \<comment> \<open>Designates some non-existent object in a category\<close>
assumes 
  S1: "E(dom x) \<longrightarrow> E x" and
  S2: "E(cod y) \<longrightarrow> E y" and
  S3: "E(x\<cdot>y) \<longleftrightarrow> dom x \<simeq> cod y" and
  S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
  S5: "x\<cdot>(dom x) \<cong> x" and
  S6: "(cod y)\<cdot>y \<cong> y" and
  SN: "\<not>(E *)"
begin  

  lemma True
    nitpick [satisfy, user_axioms, format= 2, expect=genuine, card 'a = 4-50] oops 
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True 
    nitpick [satisfy, user_axioms, expect=genuine] oops 
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  
    nitpick [satisfy, user_axioms, format= 2,  expect=genuine, card 'a = 2] oops 

lemma double_dom:
  shows "dom (dom x) \<cong> dom x"
  by (metis S1 S3 S5 S6)

lemma double_cod: 
  shows "cod (cod x) \<cong> cod x"
  by (metis S2 S3 S5 S6)

lemma cod_dom: 
  shows "cod (dom x) \<cong> dom x" 
  by (metis S1 S2 S3 S5)

lemma dom_cod: 
  shows "dom (cod x) \<cong> cod x" 
  by (metis S1 S2 S3 S6)

lemma ExDomCod: 
  assumes "E(dom x)" 
  shows "E(cod x)" and "E x" 
  apply (metis S1 S3 S6 assms) 
  by (simp add: S1 assms)

definition I :: "'a \<Rightarrow> bool" ("I _") \<comment> \<open>Identity predicate\<close>
  where "(I i) \<equiv> ((\<^bold>\<forall>x. (E(i\<cdot>x) \<^bold>\<rightarrow> (i\<cdot>x \<cong> x))) \<^bold>\<and> (\<^bold>\<forall>x. (E(x\<cdot>i) \<^bold>\<rightarrow> (x\<cdot>i \<cong> x))))" 

definition from_hom_set ("(_):\<^sub>d(_)\<rightarrow>(_)") \<comment> \<open>Predicate for testing morphism has specific domain and codomain\<close>
  where "from_hom_set x a b \<equiv> ((dom x \<simeq> a) \<and> (cod x \<simeq> b))"

abbreviation from_hom_seta ("(_):(_)\<rightarrow>(_)") \<comment> \<open>The same as before, but due to Isabelle/HOL architecture, abbreviations suit better for automated theorem proving (as an observation)\<close>
  where "x:a\<rightarrow>b \<equiv> ((dom x \<simeq> a) \<and> (cod x \<simeq> b))"

abbreviation hom_set ("\<CC>[_,_]") \<comment> \<open>Defines the set of all morphisms between specific domain and codomain\<close>
  where "\<CC>[a,b] \<equiv> {x. from_hom_set x a b}"

abbreviation par \<comment> \<open>Predicate for parallel arrows\<close>
  where "par x y \<equiv> (dom x \<simeq> dom y) \<and> (cod x \<simeq> cod y)"

lemma par_ex1: 
  assumes "par x y" 
  shows "E x" 
  using S1 assms by blast

lemma par_ex2: 
  assumes "par x y" 
  shows "E y" 
  using S1 assms by blast

lemma Ex_from_hom_set: 
  assumes "E x" 
  shows "\<^bold>\<exists>a.\<^bold>\<exists>b. (x:\<^sub>da\<rightarrow>b)" 
  by (metis (full_types) S3 S5 S6 assms from_hom_set_def) 

lemma I_from_hom_set:
  assumes "x:\<^sub>da\<rightarrow>b"
  shows "I a"
  by (smt I_def S3 S5 S6 assms double_dom from_hom_set_def)

lemma morph_hom:
  assumes "x:\<^sub>da\<rightarrow>b"
  shows "E x"
  using S2 assms from_hom_set_def by blast

lemma I_hom:
  shows "((I a) \<^bold>\<and> (E a)) \<^bold>\<leftrightarrow> (a:\<^sub>da\<rightarrow>a)"
  by (smt I_def S3 S5 S6 from_hom_set_def)

lemma comp_hom_set:
  assumes "x:\<^sub>da\<rightarrow>b" and "y:\<^sub>db\<rightarrow>c"
  shows "(y\<cdot>x):\<^sub>da\<rightarrow>c"
  by (metis S3 S4 S5 S6 assms(1) assms(2) from_hom_set_def morph_hom)

lemma Ex_two_ob1: 
  assumes "E(x\<cdot>y)" 
  shows "E x" 
  using S1 S3 assms by blast

lemma Ex_two_ob2: 
  assumes "E(x\<cdot>y)" 
  shows "E y" 
  using S2 S3 assms by blast

lemma I_dom:
  assumes "I i"
  shows "dom i \<cong> i"
  by (metis I_def S1 S3 S6 assms)

lemma Dom_I:
  assumes "dom i \<cong> i"
  shows "I i"
   by (smt I_def S3 S5 S6 assms)

definition Id :: "'a \<Rightarrow> bool" ("1(\<^sub>_)") \<comment> \<open>Another Identity predicate\<close>
  where "(1\<^sub>x) \<equiv> (dom x \<cong> x)"

abbreviation IdEx :: "'a \<Rightarrow> bool" \<comment> \<open>Existent Identity predicate\<close>
  where "(IdEx a) \<equiv> (dom a \<simeq> a)" 

lemma Id2: 
  assumes "cod x \<cong> x" 
  shows "1\<^sub>x" 
  by (metis S1 assms dom_cod local.Id_def)

lemma Id3: 
  assumes "1\<^sub>x" 
  shows "cod x \<cong> x" 
  by (metis S2 assms cod_dom local.Id_def)

definition leftinv :: "'a \<Rightarrow> bool" ("leftinv _")
  where "(leftinv x) \<equiv> (\<^bold>\<exists>y.(E(y\<cdot>x) \<^bold>\<and> Id (y\<cdot>x)))"

definition rightinv :: "'a \<Rightarrow> bool" ("rightinv _")
  where "(rightinv x) \<equiv> \<^bold>\<exists>z. (E(x\<cdot>z) \<^bold>\<and> Id (x\<cdot>z))"

definition leftinv2 :: "'a \<Rightarrow> 'a" ("leftinv2 _")
  where "(leftinv2 x) \<equiv> (SOME y.((E y) \<^bold>\<and> E(y\<cdot>x) \<^bold>\<and> Id (y\<cdot>x)))"

definition rightinv2 :: "'a \<Rightarrow> 'a" ("rightinv2 _")
  where "(rightinv2 x) \<equiv> (SOME z. (E(x\<cdot>z) \<^bold>\<and> Id (x\<cdot>z)))"

definition Iso :: "'a \<Rightarrow> bool" ("Iso _") \<comment> \<open>Isomorphism predicate\<close>
  where "(Iso x) \<equiv> (\<^bold>\<exists>y.(E(y\<cdot>x) \<and> (Id (y\<cdot>x)) \<and> (Id (x\<cdot>y))))" 

abbreviation Iso_a :: "'a \<Rightarrow> bool" ("Iso\<^sub>a _")
  where "(Iso\<^sub>a x) \<equiv> (\<^bold>\<exists>y.(E(y\<cdot>x) \<and> (Id (y\<cdot>x)) \<and> (Id (x\<cdot>y))))"

definition inv :: "'a \<Rightarrow> 'a" ("(_)\<^sup>-\<^sup>1") \<comment> \<open>Inverse morphism\<close>
  where "x\<^sup>-\<^sup>1 = (SOME y. E(y\<cdot>x) \<and> (Id(y\<cdot>x)) \<and> Id(x\<cdot>y))"

lemma Iso_a[simp]: 
  assumes "Iso x" 
  shows "Iso\<^sub>a x" 
  using Iso_def assms by blast

definition Iso\<^sub>2 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "(Iso\<^sub>2 x y) \<equiv> (E(y\<cdot>x) \<and> (Id (y\<cdot>x)) \<and> (Id (x\<cdot>y)))"

lemma check_inv: 
  assumes "rightinv x" and "leftinv x" 
  shows "Id ((leftinv2 x)\<cdot>x)" 
  by (metis (mono_tags, lifting) assms(2) leftinv2_def leftinv_def someI2_ex)

lemma check_inv2: 
  assumes "rightinv x" and "leftinv x" 
  shows "Id (x\<cdot>(rightinv2 x))" 
  by (metis (mono_tags, lifting) assms(1) rightinv2_def rightinv_def tfl_some)

lemma ExRev: 
  assumes "(E(y\<cdot>x)) \<and> (Id(y\<cdot>x)) \<and> Id(x\<cdot>y)" 
  shows "E(x\<cdot>y)"
  by (metis Ex_two_ob1 Ex_two_ob2 Id3 S4 S6 assms)

lemma inv_ex: 
  assumes "Iso x"
  shows "E((x\<^sup>-\<^sup>1)\<cdot>x)"
   by (metis (no_types, lifting) Iso_def assms local.inv_def verit_sko_ex_indirect)

lemma inv_ex20: 
  shows "(E(ix\<cdot>x) \<and> (Id (ix\<cdot>x)) \<and> (Id (x\<cdot>ix))) \<longrightarrow> E(x\<cdot>ix)" 
  using ExRev by blast

lemma inv_ex21: 
  shows "\<forall>ix. (E(ix\<cdot>x) \<and> (Id (ix\<cdot>x)) \<and> (Id (x\<cdot>ix))) \<longrightarrow> E(x\<cdot>ix)" 
  using ExRev by blast

lemma inv_ex2: 
  assumes "Iso x"
  shows "E(x\<cdot>(x\<^sup>-\<^sup>1))"
  unfolding Iso_def Id_def 
  by (metis (no_types, lifting) ExRev assms category.Iso_a category_axioms local.inv_def someI)

lemma invcheck1: 
  assumes "Iso x" 
  shows "Id ((x\<^sup>-\<^sup>1)\<cdot>x)" 
  unfolding Iso_def Id_def using Iso_def assms
  by (smt category.Id_def category_axioms inv_ex local.inv_def someI_ex)

lemma invcheck2: 
  assumes "Iso x" 
  shows "Id (x\<cdot>(x\<^sup>-\<^sup>1))" 
  unfolding Iso_def Id_def using Iso_def assms 
  by (smt Ex_two_ob2 S3 S4 S5 inv_ex invcheck1 local.Id_def)

lemma Inv_I1[simp]: 
  assumes "Iso x"
  shows "I ((x\<^sup>-\<^sup>1)\<cdot>x)" 
  using Dom_I assms invcheck1 local.Id_def by blast

lemma Inv_I2[simp]: 
  assumes "Iso x"
  shows "I (x\<cdot>(x\<^sup>-\<^sup>1))"
  using Dom_I assms invcheck2 local.Id_def by blast

lemma IsoE: 
  assumes"Iso x" 
  shows "E x" 
  using Ex_two_ob2 Iso_def assms by blast

definition inv_arrows :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<rightleftharpoons>\<^sub>d" 56) \<comment> \<open>Pair of inverse arrows\<close>
  where "x\<rightleftharpoons>\<^sub>dy \<equiv> (E(y\<cdot>x) \<and> (Id(y\<cdot>x)) \<and> Id(x\<cdot>y))" 

abbreviation inv_arrowsa :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<rightleftharpoons>" 56)
  where "x\<rightleftharpoons>y \<equiv> (E(y\<cdot>x) \<and> (Id(y\<cdot>x)) \<and> Id(x\<cdot>y))"

lemma UniqueInverses:
  assumes "x\<rightleftharpoons>y1" and "x\<rightleftharpoons>y2" 
  shows "y1 = y2" 
  by (smt S6 assms(1) assms(2) category.Ex_two_ob1 category.S3 category.S4 category.inv_ex20 category_axioms local.Id_def)

lemma UniqueInversePrep: 
  assumes "Iso\<^sub>a x" 
  shows "\<exists>!y. x \<rightleftharpoons> y" 
  using UniqueInverses assms by blast

lemma UniqueInverse: 
  assumes "Iso\<^sub>a x" 
  shows "\<not>(x\<^sup>-\<^sup>1 \<noteq> (THE y. x \<rightleftharpoons> y))"
proof
  assume "x\<^sup>-\<^sup>1 \<noteq> (THE y. x \<rightleftharpoons> y)" 
  obtain y1 where py1: "E(y1\<cdot>x) \<and> (Id(y1\<cdot>x)) \<and> Id(x\<cdot>y1)" using assms by blast
  have 1: "x \<rightleftharpoons> (x\<^sup>-\<^sup>1)" using Iso_def assms inv_ex invcheck1 invcheck2 by blast
  have 2: "\<And>y. x \<rightleftharpoons> y \<Longrightarrow> (x\<^sup>-\<^sup>1) = y" using "1" UniqueInverses by blast
  hence 3: "x\<^sup>-\<^sup>1 = (THE y. x \<rightleftharpoons> y)" by (metis (mono_tags, lifting) \<open>\<And>thesis. (\<And>y1. x \<rightleftharpoons> y1 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> the_equality)
  thus False using \<open>x\<^sup>-\<^sup>1 \<noteq> (THE y. x \<rightleftharpoons> y)\<close> by blast
qed

lemma UniqueInverseSimp[simp]: 
  assumes "Iso\<^sub>a x" 
  shows "x\<^sup>-\<^sup>1 = (THE y. x \<rightleftharpoons> y)"
  using UniqueInverse assms by blast

lemma IsoComp:
  shows "((Iso x) \<^bold>\<and> (Iso y) \<^bold>\<and> E(x\<cdot>y)) \<^bold>\<rightarrow> Iso (x\<cdot>y)"
  by (smt Id_def Iso_def S3 S4 S5 category.S6 category.leftinv_def category_axioms rightinv_def)

lemma ide_is_iso: 
  assumes "1\<^sub>x" and "E x"  
  shows "Iso x" 
  using Iso_def S5 assms(1) assms(2) local.Id_def by force

lemma Id_from_hom_set:
  assumes "x:\<^sub>da\<rightarrow>b"
  shows "1\<^sub>a"
  using assms double_dom from_hom_set_def local.Id_def by auto

lemma Id_from_hom_set2:
  assumes "x:\<^sub>da\<rightarrow>b"
  shows "1\<^sub>b"
  using assms dom_cod from_hom_set_def local.Id_def by auto

lemma Id_hom:
  shows "((Id a) \<^bold>\<and> (E a)) \<^bold>\<leftrightarrow> (a:\<^sub>da\<rightarrow>a)"
  using Dom_I I_hom Id_from_hom_set local.Id_def by blast

lemma Id_cod: 
  assumes "Id a" 
  shows "cod a \<cong> a" 
  using Id3 assms by blast

lemma Id_ex: 
  assumes "(Id a) \<^bold>\<and> (E a)" 
  shows "dom a \<simeq> a" 
  using assms local.Id_def by auto

lemma Id_ex2: 
  assumes  "dom a \<simeq> a" 
  shows "(Id a) \<^bold>\<and> (E a)" 
  using assms local.Id_def by blast

lemma Id20: 
  assumes "cod x \<simeq> x" 
  shows "IdEx x" 
  using assms dom_cod by fastforce

lemma Id30: 
  assumes "IdEx x" 
  shows "cod x \<simeq> x" 
  using assms cod_dom by fastforce

lemma Id40: 
  shows "IdEx x \<longleftrightarrow> cod x \<simeq> x" 
  using Id20 Id30 by blast

lemma Iso_hom_set: 
  assumes "Iso x" 
  shows "\<^bold>\<exists>a.\<^bold>\<exists>b. (x:\<^sub>da\<rightarrow>b)" 
  using Ex_from_hom_set Iso_def S2 S3 assms by blast

lemma Iso_inv: 
  assumes "Iso x" 
  shows "\<^bold>\<exists>y. x\<rightleftharpoons>\<^sub>dy" 
  using Iso_def assms inv_arrows_def by blast

lemma Iso_inv_dom: 
  assumes "x:\<^sub>da\<rightarrow>b" and "Iso x" 
  shows "(dom (x\<^sup>-\<^sup>1)) = b" 
  by (metis S3 assms(1) assms(2) from_hom_set_def inv_ex)

lemma dom_of_comp: 
  assumes "E (x\<cdot>y)" 
  shows "(dom (x\<cdot>y)) = (dom y)" 
  by (metis S2 S3 S4 S5 assms)

lemma cod_of_comp: 
  assumes "E (x\<cdot>y)" 
  shows "(cod (x\<cdot>y)) = (cod x)" 
  by (metis Ex_two_ob1 S3 S4 S6 assms)

lemma arrow_and_inv1: 
  assumes "x:\<^sub>da\<rightarrow>b" and "Iso x" 
  shows "((x\<^sup>-\<^sup>1)\<cdot>x) = a" 
  by (metis (no_types, lifting) Iso_def assms(1) assms(2) dom_of_comp from_hom_set_def local.Id_def local.inv_def someI_ex)

lemma Iso_inv_cod: 
  assumes "x:\<^sub>da\<rightarrow>b" and "Iso x" 
  shows "(cod (x\<^sup>-\<^sup>1)) = a" 
  by (metis arrow_and_inv1 assms(1) assms(2) cod_dom cod_of_comp from_hom_set_def)

lemma Iso_inv_hom: 
  assumes "x:\<^sub>da\<rightarrow>b" and "Iso x" 
  shows "(x\<^sup>-\<^sup>1):\<^sub>db\<rightarrow>a" 
  using Iso_inv_cod Iso_inv_dom assms(1) assms(2) from_hom_set_def by auto

abbreviation isomorphic :: "'a \<Rightarrow> 'a \<Rightarrow> bool" \<comment> \<open>Isomorphic objects (identity morphisms)\<close>
  where "isomorphic x y \<equiv> \<^bold>\<exists>f. dom f \<simeq> x \<^bold>\<and> cod f \<simeq> y \<^bold>\<and> (Iso\<^sub>a f)"

abbreviation terminal :: "'a \<Rightarrow> bool" ("terminal") \<comment> \<open>Terminal object of a category\<close>
  where "terminal x \<equiv> \<^bold>\<forall>y. ((Id y) \<longrightarrow> (\<^bold>\<exists>!z. from_hom_set z y x))" 

lemma terminal_iso: \<comment> \<open>Terminal objects are unique up to an isomorphism\<close>
  assumes "terminal x" and "terminal y" and "E x" and "E y" 
  shows "isomorphic x y" 
proof-
  have 0: "\<^bold>\<exists>!z. from_hom_set z y x"
    by (metis Ex_from_hom_set Id_from_hom_set2 assms(1) assms(2) assms(4))
  then obtain z where pz: "from_hom_set z y x" by blast
  have 1: "\<^bold>\<exists>!w. from_hom_set w x y" 
    using "0" Id_from_hom_set2 assms(2) assms(3) by blast 
  then obtain w where pw: "from_hom_set w x y" by blast
  have 2: "\<^bold>\<exists>!i. from_hom_set i x x" 
    by (meson "0" assms(1) assms(3) category.Id_from_hom_set2 category_axioms)
  then obtain i where pi: "from_hom_set i x x" by blast
  have 3: "Id i" 
    by (metis "2" Id_from_hom_set Id_hom assms(3) morph_hom pi)
  have 4: "Id x" 
    using Id_from_hom_set2 pi by auto
  have 5: "Id y" 
    using Id_from_hom_set2 pw by blast
  have 6: "i = x" 
    using "2" "4" Id_hom assms(3) morph_hom pi by blast
  have 7: "from_hom_set (z\<cdot>w) x x" 
    using comp_hom_set pw pz by blast
  have 8: "(z\<cdot>w) = x" 
    using "2" "6" "7" morph_hom pi by blast
  have 9: "Iso w" 
    by (metis (mono_tags, lifting) "5" "8" Id_hom Iso_def assms(2) assms(4) comp_hom_set morph_hom pw pz)
  have 10: "isomorphic x y" using 9 1 0 8 
    by (metis Ex_two_ob2 Iso_def from_hom_set_def pw)
  then show ?thesis 
    by blast
qed

lemma morph_hom2:  
  assumes "\<not>(E x)" 
  shows "\<not>(\<^bold>\<exists> a b. (x:\<^sub>da\<rightarrow>b))" 
  using assms morph_hom by blast

abbreviation commSquare ("commSquare") \<comment> \<open>Commutative square of arrows that goes from upper left to bottom right, and morphisms are named starting from the bottom right\<close>
  where "commSquare g p q f \<equiv> g\<cdot>p \<cong> f\<cdot>q"

abbreviation commSquareEx ("commSquareE") 
  where "commSquareE g p q f \<equiv> g\<cdot>p \<simeq> f\<cdot>q"

lemma commSquare1: 
  assumes "commSquareEx g p q f" and "commSquareEx g2 f q2 f2" and "dom g2 \<simeq> cod g" and "dom q2 \<simeq> cod q"
  shows "commSquareEx (g2\<cdot>g) p (q2\<cdot>q) f2" 
  by (metis S3 S4 assms(1) assms(2) dom_of_comp)

lemma FHS: 
  assumes "x:a\<rightarrow>b" 
  shows "x:\<^sub>da\<rightarrow>b" 
  using assms from_hom_set_def by blast

end

nitpick_params [verbose, timeout = 200]
sledgehammer_params [provers = cvc4 z3 e vampire spass remote_leo3, timeout = 300, isar_proofs = false]

declare [[smt_solver = z3]]
declare [[smt_timeout = 400]]

declare [[smt_solver = cvc4]]
declare [[smt_timeout = 400]]
declare [[smt_oracle]]

section \<open>Opposite category\<close>

locale opposite_category = 
A: category domain codomain composition *
for 
  domain :: "'a \<Rightarrow> 'a" ("dom _") and
  codomain :: "'a \<Rightarrow> 'a" ("cod _") and
  composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*")
begin

abbreviation domop :: "'a \<Rightarrow> 'a"  
  where "(domop x) \<equiv> (codomain x)" 

abbreviation codop :: "'a \<Rightarrow> 'a"  
  where "(codop x) \<equiv> (domain x)" 

abbreviation compositionop :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<cdot>op" 110)
  where "x \<cdot>op y \<equiv> y \<cdot> x" 

lemma dom_simp[simp]: 
  shows "(codomain x) = (domop x)" 
  by auto

lemma cod_simp[simp]: 
  shows "(domain x) = (codop x)" 
  by auto

lemma comp_simp[simp]: 
  shows "x \<cdot> y = y \<cdot>op x"
  by auto

lemma ide_simp[simp]: 
  shows "(1\<^sub>x) \<longleftrightarrow> A.Id(x)" 
  by simp

interpretation category domop codop compositionop *
  apply unfold_locales
  using A.S2 apply blast 
  using A.S1 apply blast
  apply (metis A.S3) 
  using A.S4 apply metis 
  using A.S6 apply blast 
  using A.S5 apply blast
  using A.SN by auto

lemma iscategory: 
  shows "category domop codop compositionop *" 
  using category_axioms by blast

end

sublocale opposite_category \<subseteq> category domop codop compositionop *
  using iscategory by blast

section \<open>Product category\<close>

locale productCategory =
A: category domain codomain composition nonex +
B: category domain' codomain' composition' nonex'
for 
  domain :: "'a \<Rightarrow> 'a" ("dom _") and
  codomain :: "'a \<Rightarrow> 'a" ("cod _") and
  composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<cdot>" 110) and
  nonex :: "'a" ("*") and
  domain' :: "'b \<Rightarrow> 'b" ("dom2 _") and
  codomain' :: "'b \<Rightarrow> 'b" ("cod2 _") and
  composition' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infix "\<cdot>2" 110) and 
  nonex' :: "'b" ("*2") +
assumes
  Ex:"(E (x::'a) \<and> E (y::'b)) \<longleftrightarrow> E(x,y)" and
  Ex2:"(E (x::'a) \<and> E (y::'b)) \<longleftrightarrow> E(y,x)"

begin 

 lemma True
    nitpick [satisfy, user_axioms, format= 2, expect=genuine, card i = 4-50, timeout = 10] oops 

abbreviation (input) Dom :: "('a * 'b) \<Rightarrow> ('a * 'b)"
  where "Dom x \<equiv> ((dom (fst x)), dom2 (snd x))"

abbreviation (input) Cod :: "('a * 'b) \<Rightarrow> ('a * 'b)"
  where "Cod x \<equiv> ((cod (fst x)), cod2 (snd x))"

abbreviation (input) Composition :: "('a * 'b) \<Rightarrow> ('a * 'b) \<Rightarrow> ('a * 'b)" (infix "\<bullet>" 110)
  where "Composition x y \<equiv> ((fst x)\<cdot>(fst y),(snd x)\<cdot>2(snd y))"

abbreviation (input) Nonex :: "'a*'b" 
  where "Nonex \<equiv> (*,*2)"

abbreviation (input) Ide :: "('a * 'b) \<Rightarrow> bool"
  where "Ide x \<equiv> A.Id (fst x) \<and> B.Id (snd x)"

lemma Dom_comp :
  assumes "E (Composition x y)"
  shows "Dom (Composition x y) = Dom y"
  using A.dom_of_comp B.dom_of_comp Ex assms by fastforce

lemma Cod_comp :
  assumes "E (Composition x y)"
  shows "Cod (Composition x y) = Cod x"
  using A.cod_of_comp B.cod_of_comp Ex assms by fastforce

lemma prod_S1:
  shows "E(Dom x) \<longrightarrow> E x"
  by (metis A.S1 B.S1 Ex prod.exhaust_sel)

lemma prod_S2:
  shows "E(Cod x) \<longrightarrow> E x"
  by (metis A.S2 B.S2 Ex prod.exhaust_sel)

lemma prod_S3:
  shows "E(Composition x y) \<longleftrightarrow> Dom x \<simeq> Cod y"
  using A.S3 B.S3 Ex by blast

lemma prod_S4:
  shows "x\<bullet>(y\<bullet>z) \<cong> (x\<bullet>y)\<bullet>z"
  by (smt A.S4 B.S3 B.S4 Ex fst_eqD prod_S1 prod_S2 snd_eqD)

lemma prod_S5:
  shows "x\<bullet>(Dom x) \<cong> x"
  by (metis A.S5 B.S5 Ex prod.exhaust_sel snd_conv swap_simp)

lemma prod_S6:
  shows "(Cod y)\<bullet>y \<cong> y"
  by (smt A.S6 B.S3 B.S6 Ex prod.collapse prod.sel(1) prod.sel(2) prod_S3)

theorem product_is_category:
  shows "category Dom Cod Composition (*,*2)"
proof 
  fix x
  show "E(Dom x) \<longrightarrow> E x"
    using prod_S1  by blast
  show "E(Cod x) \<longrightarrow> E x"
    using prod_S2 by blast
  fix y
  show "E(Composition x y) \<longleftrightarrow> Dom x \<simeq> Cod y"
    using prod_S3 by blast
  fix z
  show "x\<bullet>(y\<bullet>z) \<cong> (x\<bullet>y)\<bullet>z"
    using prod_S4 by blast
  show "x\<bullet>(Dom x) \<cong> x"
    using prod_S5 by blast
  show "(Cod y)\<bullet>y \<cong> y"
    using prod_S6 by blast
  show "\<not> (E (*, *2))" using A.SN Ex by blast
qed

end

sublocale productCategory \<subseteq> category Dom Cod Composition Nonex
  using product_is_category by auto

end