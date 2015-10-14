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
definition MakeCatLeftProjection where
  "MakeCatLeftProjection C \<equiv> MakeCat \<lparr>
      Obj = fst ` Obj C,
      Mor = fst ` Mor C,
      Dom = \<lambda>f. fst (Dom C (f, SOME g. True)),
      Cod = \<lambda>f. fst (Cod C (f, SOME g. True)),
      Id = \<lambda>X. fst (Id C (X, SOME X'. True)),
      Comp =
        \<lambda>f f'. fst (Comp C (f, SOME g. True) (f', SOME g'. True))
  \<rparr>"

definition LeftProjectionFtor' where
  "LeftProjectionFtor' C \<equiv> \<lparr>
    CatDom = C,
    CatCod = MakeCatLeftProjection C,
    MapM = \<lambda>(f1, f2). f1
  \<rparr>"

(*
definition 
  MakeCat :: "('o,'m,'a) Category_scheme \<Rightarrow> ('o,'m,'a) Category_scheme" where
  "MakeCat C \<equiv> \<lparr>
      Obj = Obj C , 
      Mor = Mor C , 
      Dom = restrict (Dom C) (Mor C) , 
      Cod = restrict (Cod C) (Mor C) , 
      Id  = restrict (Id C) (Obj C) , 
      Comp = \<lambda> f g . (restrict (split (Comp C)) ({(f,g) | f g . f \<approx>>\<^bsub>C\<^esub> g})) (f,g), 
      \<dots> = Category.more C
  \<rparr>"
*)

lemma ExtentionalityClosure:
  assumes "Category C"
  shows "MakeCat C = C"

proof -
  { have "Obj C = Obj (MakeCat C)"
    using assms
    by (simp add: MakeCatObj)    
  }
  next { have "Mor C = Mor (MakeCat C)"
    using assms
    by (simp add: MakeCatMor)
  }
  next { have "Dom C = Dom (MakeCat C)"
    using assms (* lemma MakeCatDom: "f \<in> mor\<^bsub>C\<^esub> \<Longrightarrow> dom\<^bsub>C\<^esub> f = dom\<^bsub>MakeCat C\<^esub> f" *)
    sorry
  }
  next { have "Cod C = Cod (MakeCat C)"
    sorry
  }
  next { have "Id C = Id (MakeCat C)"
    sorry
  }
  next { have "Comp C = Comp (MakeCat C)"
    sorry
  }
  then show ?thesis sorry
qed

lemma
  assumes "Category C1"
  and "Category C2"
  and "Obj C2 \<noteq> {}"
  and "Mor C2 \<noteq> {}"
  shows "MakeCatLeftProjection (ProductCategory C1 C2) = C1"
unfolding MakeCatLeftProjection_def
unfolding MakeCat_def

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