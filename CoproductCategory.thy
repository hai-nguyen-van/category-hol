theory CoproductCategory

imports
  Main
  "Category2/Category"
  "Category2/Functors"
  "ProductCategory"
  
begin

definition DiagonalFunctor' where
  "DiagonalFunctor' C \<equiv> \<lparr>
      CatDom = C,
      CatCod = ProductCategory C C,
      MapM = \<lambda>m. (m, m)
  \<rparr>"

definition DiagonalFunctor where
  "DiagonalFunctor C \<equiv> MakeFtor (DiagonalFunctor' C)"

abbreviation "\<Delta>' C \<equiv> DiagonalFunctor' C"
abbreviation "\<Delta> C \<equiv> DiagonalFunctor C"

(* Step 0 *)
lemma DiagonalFtor'Obj:
  assumes "Category C"
  assumes X_ext: "X \<in> obj\<^bsub>C\<^esub>"
  shows "\<Delta>' C @@ X = (X, X)"  
  apply (simp add: MapO_def DiagonalFunctor'_def ProductCategory_def MakeCat_def)
  apply (rule the_equality, auto)
  using assms
  by (simp add: Category.IdInj)+


(* Step 1: Proof that (\<Delta>' C) is prefunctor *)
lemma DiagonalFtor'PreFunctor:
  assumes "Category C"
  shows "PreFunctor (\<Delta>' C)"
unfolding PreFunctor_def
proof (intro conjI)
  show "Category (CatDom (\<Delta>' C))" using assms by (auto simp add: DiagonalFunctor'_def)
  next show "Category (CatCod (\<Delta>' C))" using assms by (auto simp add: DiagonalFunctor'_def ProductCategory.ProductClosure)
  next show "\<forall>f g. f \<approx>>\<^bsub>CatDom (\<Delta>' C)\<^esub> g \<longrightarrow>
          \<Delta>' C ## (f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g) =
          (\<Delta>' C ## f) ;;\<^bsub>CatCod (\<Delta>' C)\<^esub> (\<Delta>' C ## g)"
    proof -
      { assume f_g_ext: "f \<approx>>\<^bsub>CatDom (\<Delta>' C)\<^esub> g"
        have "\<And>f g. \<Delta>' C ## (f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g) = (f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g, f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g)"
        by (auto simp: DiagonalFunctor'_def)
      }
      next { 
        have "\<And>f g. (\<Delta>' C ## f) ;;\<^bsub>CatCod (\<Delta>' C)\<^esub> (\<Delta>' C ## g) = (f, f) ;;\<^bsub>CatCod (\<Delta>' C)\<^esub> (g, g)"
        by (auto simp: DiagonalFunctor'_def)
      }
      next {
        fix f g
        assume f_g_ext: "f \<approx>>\<^bsub>CatDom (\<Delta>' C)\<^esub> g"
        have "(f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g, f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g) = (f, f) ;;\<^bsub>CatCod (\<Delta>' C)\<^esub> (g, g)"
        using assms f_g_ext
        apply (simp add: Category.CompDefined_def DiagonalFunctor'_def ProductCategory_def, auto)
        by (simp add: MakeCat_def, auto)
      }
      then show ?thesis using assms by (simp add: DiagonalFunctor'_def)
    qed
  next show "\<forall>X. X \<in> obj\<^bsub>CatDom (\<Delta>' C)\<^esub> \<longrightarrow>
        (\<exists>Y\<in>obj\<^bsub>CatCod (\<Delta>' C)\<^esub>.
            \<Delta>' C ## id\<^bsub>CatDom (\<Delta>' C)\<^esub> X = id\<^bsub>CatCod (\<Delta>' C)\<^esub> Y)"
    proof - (* (intro allI impI) *)
      (* LEMME 1 *)
      { have "\<And>X. \<Delta>' C ## id\<^bsub>CatDom (\<Delta>' C)\<^esub> X = (id\<^bsub>CatDom (\<Delta>' C)\<^esub> X, id\<^bsub>CatDom (\<Delta>' C)\<^esub> X)"
        using assms by (simp add:DiagonalFunctor'_def)
      }
      (* LEMME 2 *)
      next {
        fix X
        assume X_ext: "X \<in> obj\<^bsub>CatDom (\<Delta>' C)\<^esub>"
        have "\<Delta>' C @@ X = (X, X)"
        using assms X_ext
          apply (simp add: MapO_def DiagonalFunctor'_def ProductCategory_def MakeCat_def)
          apply (rule the_equality, auto)
          by (simp add: Category.IdInj)+
      }
      (* LEMME 3 *)
      next { fix X
        assume X_ext: "X \<in> obj\<^bsub>CatDom (\<Delta>' C)\<^esub>"
        have "id\<^bsub>CatCod (\<Delta>' C)\<^esub> (X, X) = (id\<^bsub>CatDom (\<Delta>' C)\<^esub> X, id\<^bsub>CatDom (\<Delta>' C)\<^esub> X)"
        using assms X_ext
        by (simp add: DiagonalFunctor'_def ProductCategory_def MakeCat_def)
      }
      (* LEMME 4 *)
      next { fix X
        assume X_ext: "X \<in> obj\<^bsub>CatDom (\<Delta>' C)\<^esub>"
        have "\<Delta>' C ## id\<^bsub>CatDom (\<Delta>' C)\<^esub> X = id\<^bsub>CatCod (\<Delta>' C)\<^esub> (X, X)"
        using assms X_ext
        by (simp add: DiagonalFunctor'_def ProductCategory_def MakeCat_def)
      }
      then show ?thesis
        by (metis (no_types, lifting) Category.select_convs(1) DiagonalFunctor'_def Functor.select_convs(1) Functor.select_convs(2) MakeCatObj ProductCategory_def SigmaI)
    qed
  qed

(* Step 2: Show that functors applied to arrows are distributed over dom and cod of arrow *)
lemma DiagonalFtor'FtorM:  
  assumes "Category C"
  shows "FunctorM (DiagonalFunctor' C)"
proof (auto simp add: FunctorM_def IdFtor'PreFunctor assms FunctorM_axioms_def)
  {
    fix f X Y
    assume a: "f maps\<^bsub>CatDom (\<Delta>' C)\<^esub> X to Y" 
    show "((\<Delta>' C) ## f) maps\<^bsub>CatCod (\<Delta>' C)\<^esub> ((\<Delta>' C) @@ X) to ((\<Delta>' C) @@ Y)"
    proof -
      have "X \<in> obj\<^bsub>CatDom (\<Delta>' C)\<^esub>" and "Y \<in> obj\<^bsub>CatDom (\<Delta>' C)\<^esub>"
        using a assms
        by (simp add: Category.MapsToObj DiagonalFunctor'_def)+
      moreover have "\<Delta>' C ## f \<in> mor\<^bsub>CatCod (\<Delta>' C)\<^esub>"
        using a assms
        by (simp add: DiagonalFunctor'_def ProductCategory_def MakeCat_def, auto)
      moreover have "dom\<^bsub>CatCod (\<Delta>' C)\<^esub> (\<Delta>' C ## f) = \<Delta>' C @@ X"
        proof -
          have "\<Delta>' C @@ X = (X, X)"
            by (metis DiagonalFtor'Obj DiagonalFunctor'_def Functor.select_convs(1) assms calculation(1))
          moreover have "dom\<^bsub>CatCod (\<Delta>' C)\<^esub> (\<Delta>' C ## f) = (X, X)"
            using assms a
            by (simp add: DiagonalFunctor'_def ProductCategory_def MakeCat_def, auto)
          ultimately show ?thesis by simp
          qed
      moreover have "cod\<^bsub>CatCod (\<Delta>' C)\<^esub> (\<Delta>' C ## f) = \<Delta>' C @@ Y"
        proof -
          have "\<Delta>' C @@ Y = (Y, Y)"
            by (metis DiagonalFtor'Obj DiagonalFunctor'_def Functor.select_convs(1) assms calculation(2))
          moreover have "cod\<^bsub>CatCod (\<Delta>' C)\<^esub> (\<Delta>' C ## f) = (Y, Y)"
            using assms a
            by (simp add: DiagonalFunctor'_def ProductCategory_def MakeCat_def, auto)
          ultimately show ?thesis by simp
          qed
      ultimately show ?thesis using assms a by blast
    qed
  }
  show "PreFunctor (\<Delta>' C)" using assms by (rule DiagonalFtor'PreFunctor)
qed

(* Step 3 : Final gather *)
lemma DiagonalFtorFtor:  "Category C \<Longrightarrow> Functor (\<Delta> C)"
by (auto simp add: DiagonalFunctor_def DiagonalFtor'FtorM intro: MakeFtor)


end