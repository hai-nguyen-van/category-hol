theory ProductCategory

imports
  Main
  "Category2/Category"
  "Category2/Functors"
  
begin

value "OppositeCategory"

section "Products of Categories"

subsection "Basic construction"
text{* We define the cartesian product of two categories as: *}

definition ProductCategory :: "('o1, 'm1, 'a1) Category_scheme \<Rightarrow> ('o2, 'm2, 'a2) Category_scheme \<Rightarrow> ('o1 \<times> 'o2, 'm1 \<times> 'm2) Category" where
  "ProductCategory C1 C2 \<equiv> MakeCat \<lparr>
    Obj = Obj C1 \<times> Obj C2,
    Mor = Mor C1 \<times> Mor C2,
    Dom = \<lambda>(f1, f2). (Dom C1 f1, Dom C2 f2),
    Cod = \<lambda>(f1, f2). (Cod C1 f1, Cod C2 f2),
    Id = \<lambda>(o1, o2). (Id C1 o1, Id C2 o2),
    Comp = \<lambda>(f, g) (f', g'). (Comp C1 f f', Comp C2 g g')
  \<rparr>"

text{* Categories are closed under product: *}
theorem ProductClosure:
  assumes "Category C1"
  and "Category C2"
  shows "Category (ProductCategory C1 C2)"
apply (simp add: ProductCategory_def)
apply (rule MakeCat)
apply (unfold_locales)
apply (auto)

apply (simp add: Category.Cdom assms(1))
apply (simp add: Category.Cdom assms(2))
apply (simp add: Category.Ccod assms(1))
apply (simp add: Category.Ccod assms(2))
apply (simp add: Category.CatIdDomCod(1) Category.CatIdDomCod(2) Category.CatIdInMor MapsTo_def assms(1) assms(2))
apply (simp add: Category.Cidl assms(1))
apply (simp add: Category.Cidl assms(2))
apply (simp add: Category.Cidr assms(1))
apply (simp add: Category.Cidr assms(2))

apply (smt Category.Cassoc Category.select_convs(2) Category.select_convs(3) Category.select_convs(4) CompDefinedE CompDefinedI SigmaD1 assms(1) old.prod.case prod.inject)
apply (metis (no_types, lifting) Category.Cassoc Category.select_convs(2) Category.select_convs(3) Category.select_convs(4) CompDefinedE CompDefinedI SigmaD2 assms(2) old.prod.case prod.inject)
apply (smt Category.MapsToMorDomCod(1) Category.MapsToMorDomCod(2) Category.MapsToMorDomCod(3) Category.select_convs(2) Category.select_convs(3) Category.select_convs(4) CompDefinedI MapsTo_def SigmaD1 SigmaD2 SigmaI assms(1) assms(2) old.prod.case prod.inject)
done

subsection "Left and Right Projection Functors"
text{* We now define left and right projection functors for product categories *}

(* Let [C], [D] two categories. [ProductLeftProjectionFunctor] maps product category [C] \<times> [D] to [C] *)
definition MakeProductLeftProjection where
  "MakeProductLeftProjection C \<equiv> MakeCat \<lparr>
      Obj = fst ` Obj C,
      Mor = fst ` Mor C,
      Dom = \<lambda>f. fst (Dom C (f, SOME g. True)),
      Cod = \<lambda>f. fst (Cod C (f, SOME g. True)),
      Id = \<lambda>X. fst (Id C (X, SOME X'. True)),
      Comp =
        \<lambda>f f'. fst (Comp C (f, SOME g. True) (f', SOME g'. True))
  \<rparr>"


lemma CatMorProductLeftProjection:
  assumes "Category C"
  and "Category D"
  and "(f, g) \<in> Mor (ProductCategory C D)"
  shows "f \<in> Mor C"
by (metis Category.select_convs(2) MakeCatMor ProductCategory_def SigmaD1 assms(3))

lemma CatMorProductRightProjection:
  assumes "Category C"
  and "Category D"
  and "(f, g) \<in> Mor (ProductCategory C D)"
  shows "g \<in> Mor D"
by (metis Category.select_convs(2) MakeCatMor ProductCategory_def SigmaD2 assms(3))

lemma CatDomProductLeftProjection:
  assumes "Category C"
  and "Category D"
  and "(f, g) \<in> Mor (ProductCategory C D)"
  shows "fst (Dom (ProductCategory C D) (f, g)) = Dom C f"
proof -
  have f_is_mor: "f \<in> Mor C" using assms by (rule CatMorProductLeftProjection)
  have g_is_mor: "g \<in> Mor D" using assms by (rule CatMorProductRightProjection)
  have 1: "Dom (ProductCategory C D) = (\<lambda>(f1, f2)\<in>(mor\<^bsub>C\<^esub>) \<times> (mor\<^bsub>D\<^esub>). (dom\<^bsub>C\<^esub> f1, dom\<^bsub>D\<^esub> f2))" by (simp add: ProductCategory_def MakeCat_def)
  have 2:"(\<lambda>(f1, f2)\<in>(mor\<^bsub>C\<^esub>) \<times> (mor\<^bsub>D\<^esub>). (dom\<^bsub>C\<^esub> f1, dom\<^bsub>D\<^esub> f2)) (f, g) = (dom\<^bsub>C\<^esub> f, dom\<^bsub>D\<^esub> g)" using f_is_mor g_is_mor by (auto)
  have 3: "Dom (ProductCategory C D) (f, g) = (Dom C f, Dom D g)" using 1 2 by (auto)
  thus ?thesis by (auto)
qed

(* Le fait que Obj D est-il vraiment contraignant ? *)
lemma CatObjProductLeftProjection:
  assumes "Category C"
  and "Category D"
  and "Obj D \<noteq> {}"
  shows "fst ` (Obj (ProductCategory C D)) = Obj C"
proof -
  have "Obj (ProductCategory C D) = Obj C \<times> Obj D" by (simp add: ProductCategory_def MakeCat_def)
  thus ?thesis using assms by auto
qed



lemma MakeCatSelfClosure:
  assumes "Category C"
  shows "C = MakeCat \<lparr>
    Obj = Obj C, Mor = Mor C,
        Dom = Dom C,
        Cod = Cod C,
        Id = Id C,
        Comp = Comp C
  \<rparr>"
apply (unfold_locales)
unfolding MakeCat_def
proof -
  have "Dom C = restrict (Dom \<lparr>Obj = obj\<^bsub>C\<^esub>, Mor = mor\<^bsub>C\<^esub>, Dom = Dom C, Cod = Cod C, Id = Category.Id C, Comp = op ;;\<^bsub>C\<^esub>\<rparr>)
                  (mor\<^bsub>\<lparr>Obj = obj\<^bsub>C\<^esub>, Mor = mor\<^bsub>C\<^esub>, Dom = Dom C, Cod = Cod C, Id = Category.Id C, Comp = op ;;\<^bsub>C\<^esub>\<rparr>\<^esub>)"
    apply (simp add: restrict_def)
    apply (rule ext)
    proof -
    have "x \<in> Mor C"

apply (simp add: MakeCat_def, auto)

sledgehammer[provers="cvc4 remote_vampire z3 spass e alt_ergo verit cvc3", verbose]


lemma
  assumes "Category C1"
  and "Category C2"
  and "Obj C2 \<noteq> {}"
  and "Mor C2 \<noteq> {}"
  shows "MakeProductLeftProjection (ProductCategory C1 C2) = C1"
unfolding MakeProductLeftProjection_def

(* HERE *)
proof -
  have "fst ` (obj\<^bsub>ProductCategory C1 C2\<^esub>) = Obj C1" using assms by (simp add: ProductCategory_def MakeCat_def)
  have "fst ` (mor\<^bsub>ProductCategory C1 C2\<^esub>) = Mor C1" using assms by (simp add: ProductCategory_def MakeCat_def)
  have "(\<lambda>f. fst (dom\<^bsub>ProductCategory C1 C2\<^esub> (f, SOME g. True))) = Dom C1"


(*
    sledgehammer supported_provers
    sledgehammer[provers="cvc4 remote_vampire z3 spass e alt_ergo verit cvc3", verbose]
    (* sledgehammer[provers="alt_ergo", verbose] *)
    sledgehammer[provers="cvc3", smt_trace, verbose]
*)
    
    by (simp add: ProductCategory_def MakeCat_def, auto)
apply (subst CatObjProductLeftProjection)
apply (subst CatDomProductLeftProjection)

  


theorem LeftProjectionClosure:
  assumes "Category C1"
  and "Category C2"
  and "Obj C2 \<noteq> {}"
  shows "Category (MakeProductLeftProjection (ProductCategory C1 C2))"

(*
apply (simp add: ProductCategory_def MakeProductLeftProjection_def)
apply (rule MakeCat)
apply (unfold_locales)
apply (auto)
*)

unfolding Category_def
unfolding ExtCategory_def
unfolding Category_axioms_def

proof (intro conjI)
  have ax1: "Dom (MakeProductLeftProjection (ProductCategory C1 C2)) = Dom C1"
    using assms
    sorry
    sledgehammer supported_provers
    
    by (simp add: ProductCategory_def MakeProductLeftProjection_def MakeCat_def, auto)


  have " Dom (MakeProductLeftProjection (ProductCategory C1 C2)) \<in> extensional (mor\<^bsub>MakeProductLeftProjection (ProductCategory C1 C2)\<^esub>)"
    






definition ProductLeftProjectionFunctor where
  "ProductLeftProjectionFunctor C \<equiv>
    MakeFtor \<lparr>
      CatDom = C,
      CatCod = MakeProductLeftProjection C,
      MapM = \<lambda>(m1, m2). m1
  \<rparr>"



end