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

lemma "\<And>X. X \<in> obj\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> \<Longrightarrow>
         \<exists>Y.
            DiagonalFunctor' C ## id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X =
            id\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> Y"
apply (rule exI)
oops 

lemma "(\<And>X. P X) \<Longrightarrow> \<forall>X. P X"
by auto

lemma "(P ==> Q) ==> P-->Q"

lemma DiagonalFtor'PreFunctor:
  assumes "Category C"
  shows "PreFunctor (DiagonalFunctor' C)"
unfolding PreFunctor_def
proof (intro conjI)
  have "Category (CatDom (DiagonalFunctor' C))" using assms by (auto simp add: DiagonalFunctor'_def)
  have "Category (CatCod (DiagonalFunctor' C))" using assms by (auto simp add: DiagonalFunctor'_def ProductCategory.ProductClosure)
  have "\<forall>f g. f \<approx>>\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> g \<longrightarrow>
          DiagonalFunctor' C ## (f ;;\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> g) =
          (DiagonalFunctor' C ## f) ;;\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> (DiagonalFunctor' C ## g)"
    proof -
      have "\<And>f g. DiagonalFunctor' C ## (f ;;\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> g) = (f ;;\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> g, f ;;\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> g)"
        using assms by (simp add: DiagonalFunctor'_def)
      moreover have "\<And>f g. (DiagonalFunctor' C ## f) ;;\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> (DiagonalFunctor' C ## g) = (f, f) ;;\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> (g, g)"
        using assms by (simp add: DiagonalFunctor'_def)
      moreover have "\<And>f g. (f ;;\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> g, f ;;\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> g) = (f, f) ;;\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> (g, g)"
        using assms sorry
      ultimately show ?thesis by auto
    qed
  have "\<forall>X. X \<in> obj\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> \<longrightarrow>
        (\<exists>Y\<in>obj\<^bsub>CatCod (DiagonalFunctor' C)\<^esub>.
            DiagonalFunctor' C ## id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X = id\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> Y)"
    proof (intro allI impI)
      have "\<And>X. DiagonalFunctor' C ## id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X = (id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X, id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X)"
        using assms by (simp add:DiagonalFunctor'_def)
      have "\<And>X. id\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> (X, X) = (id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X, id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X)"
        using assms sledgehammer
      have "\<And>X. DiagonalFunctor' C ## id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X = id\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> (X, X)"
        sledgehammer
        (* HERE *)
    apply (auto)
    apply (rule_tac x=X in bexI)
    apply (auto)

end