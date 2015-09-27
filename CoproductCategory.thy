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

abbreviation "\<Delta>' C \<equiv> DiagonalFunctor' C"

definition DiagonalFunctor where
  "DiagonalFunctor C \<equiv> MakeFtor (DiagonalFunctor' C)"

abbreviation "\<Delta> C \<equiv> DiagonalFunctor C"

lemma "\<And>X. X \<in> obj\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> \<Longrightarrow>
         \<exists>Y.
            DiagonalFunctor' C ## id\<^bsub>CatDom (DiagonalFunctor' C)\<^esub> X =
            id\<^bsub>CatCod (DiagonalFunctor' C)\<^esub> Y"
apply (rule exI)
oops 

(*
\<And>f g. Category C \<Longrightarrow>
           (f ;;\<^bsub>C\<^esub> g, f ;;\<^bsub>C\<^esub> g) =
           (f, f) ;;\<^bsub>MakeCat \<lparr>Obj = (obj\<^bsub>C\<^esub>) \<times> (obj\<^bsub>C\<^esub>), Mor = (mor\<^bsub>C\<^esub>) \<times> (mor\<^bsub>C\<^esub>), Dom = \<lambda>(f1, f2). (dom\<^bsub>C\<^esub> f1, dom\<^bsub>C\<^esub> f2), Cod = \<lambda>(f1, f2). (cod\<^bsub>C\<^esub> f1, cod\<^bsub>C\<^esub> f2), Id = \<lambda>(o1, o2). (id\<^bsub>C\<^esub> o1, id\<^bsub>C\<^esub> o2), Comp = \<lambda>(f, g) (f', g'). (f ;;\<^bsub>C\<^esub> f', g ;;\<^bsub>C\<^esub> g')\<rparr>\<^esub>
           (g, g)
*)
find_theorems "THE _ . _ = _"

lemma MakeCat_extract:
  assumes "Category C"
  and "f \<in> Mor C"
  and "g \<in> Mor C"
  shows "f ;;\<^bsub>C\<^esub> g = (Comp C) f g"
by auto


lemma "P(x) \<and> Q(x)"
proof (intro conjI)
  fix x P Q
  show 1: "P x" sorry
  next show 2: "Q x" sorry
qed

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
      { fix f g
        assume f_g_ext: "f \<approx>>\<^bsub>CatDom (\<Delta>' C)\<^esub> g"
        have "\<And>f g. \<Delta>' C ## (f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g) = (f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g, f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g)"
        by (auto simp: DiagonalFunctor'_def)
      }
      next { fix f g
        have "\<And>f g. (\<Delta>' C ## f) ;;\<^bsub>CatCod (\<Delta>' C)\<^esub> (\<Delta>' C ## g) = (f, f) ;;\<^bsub>CatCod (\<Delta>' C)\<^esub> (g, g)"
        by (auto simp: DiagonalFunctor'_def)
      }
      next { fix f g
        have "\<And>f g. (f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g, f ;;\<^bsub>CatDom (\<Delta>' C)\<^esub> g) = (f, f) ;;\<^bsub>CatCod (\<Delta>' C)\<^esub> (g, g)"
        sorry
      }
      then show ?thesis using assms by (simp add: DiagonalFunctor'_def)
    qed
  next show "\<forall>X. X \<in> obj\<^bsub>CatDom (\<Delta>' C)\<^esub> \<longrightarrow>
        (\<exists>Y\<in>obj\<^bsub>CatCod (\<Delta>' C)\<^esub>.
            \<Delta>' C ## id\<^bsub>CatDom (\<Delta>' C)\<^esub> X = id\<^bsub>CatCod (\<Delta>' C)\<^esub> Y)"
    proof - (* (intro allI impI) *)
      { fix X
        have "\<And>X. \<Delta>' C ## id\<^bsub>CatDom (\<Delta>' C)\<^esub> X = (id\<^bsub>CatDom (\<Delta>' C)\<^esub> X, id\<^bsub>CatDom (\<Delta>' C)\<^esub> X)"
        using assms by (simp add:DiagonalFunctor'_def)
        }
      next { fix X
        have "\<And>X. \<Delta>' C @@ X = (X, X)"
        using assms
          apply (simp add: MapO_def DiagonalFunctor'_def ProductCategory_def MakeCat_def)
          apply (rule the_equality)
          apply auto
          (* 1. hypothèse précédente, 2. et 3. unicité de l'identité par rapport aux objets*)
          sorry
        }
      next { fix X
        have "\<And>X. id\<^bsub>CatCod (\<Delta>' C)\<^esub> (X, X) = (id\<^bsub>CatDom (\<Delta>' C)\<^esub> X, id\<^bsub>CatDom (\<Delta>' C)\<^esub> X)"
        using assms sorry
      }
      next { fix X
        have "\<And>X. \<Delta>' C ## id\<^bsub>CatDom (\<Delta>' C)\<^esub> X = id\<^bsub>CatCod (\<Delta>' C)\<^esub> (X, X)"
        using assms sorry
      }
      then show ?thesis using assms
        by (metis (no_types, lifting) Category.select_convs(1) DiagonalFunctor'_def Functor.select_convs(1) Functor.select_convs(2) MakeCatObj ProductCategory_def SigmaI)
    qed
        (* HERE : pas fini *)
  qed
end