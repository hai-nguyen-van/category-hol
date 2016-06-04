theory FunctorComposition

imports
  Main
  "Category2/Category"
  "Category2/Functors"

begin

(* Compostion of two functors *)
definition FtorComp' :: "
  ('o2, 'o3, 'm2, 'm3, 'b, 'c, 'e) Functor_scheme \<Rightarrow>
  ('o1, 'o2, 'm1, 'm2, 'a, 'b, 'd) Functor_scheme \<Rightarrow>
  ('o1, 'o3, 'm1, 'm3, 'a, 'c) Functor
  " where
  "FtorComp' G F \<equiv> \<lparr> 
    CatDom = CatDom F,
    CatCod = CatCod G,
    MapM = \<lambda>f. (G ## (F ## f))
  \<rparr>"

definition FtorComp (infixl "\<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r" 55) where
  "G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F = MakeFtor (FtorComp' G F)"

(* Step 0: Simplification rules for dom and cod over functor composition *)
lemma DomFtorComp:
  assumes "Functor F"
  and "Functor G"
  and "CatCod F = CatDom G"
  shows "CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) = CatDom F"
unfolding FtorComp_def MakeFtor_def FtorComp'_def
by (auto)

lemma CodFtorComp:
  assumes "Functor F"
  and "Functor G"
  and "CatCod F = CatDom G"
  shows "CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) = CatCod G"
unfolding FtorComp_def MakeFtor_def FtorComp'_def
by (auto)

(* Step 1: Proof that (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) is prefunctor *)
lemma FtorComp'PreFunctor:
  assumes "Functor F"
  and "Functor G"
  and "CatCod F = CatDom G"
  shows "PreFunctor (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)"
unfolding PreFunctor_def
proof (intro conjI)
  show "\<forall>f g. f \<approx>>\<^bsub>CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> g \<longrightarrow>
          (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f ;;\<^bsub>CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> g =
          (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f ;;\<^bsub>CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub>
          ((G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## g)"
    using assms by (smt Category.MapsToMorDomCod(1) CompDefinedE FtorComp'_def FtorComp_def Functor.FunctorCompDef Functor.select_convs(1) Functor.select_convs(2) Functor.select_convs(3) MakeFtorMor MakeFtor_def PreFunctor.CatDom PreFunctor.FunctorComp PreFunctorFunctor)
  next show "\<forall>X. X \<in> obj\<^bsub>CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> \<longrightarrow>
        (\<exists>Y\<in>obj\<^bsub>CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub>.
            (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## id\<^bsub>CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> X =
            id\<^bsub>CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> Y)"
    using assms by (smt Category.CatIdInMor FtorComp'_def FtorComp_def Functor.select_convs(1) Functor.select_convs(2) Functor.select_convs(3) MakeFtorMor MakeFtor_def PreFunctor.CatDom PreFunctor.FunctorId2 PreFunctorFunctor)
  next show "Category (CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F))"
    using assms by (simp add: FtorComp'_def FtorComp_def MakeFtor_def)
  next show "Category (CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F))"
    using assms by (simp add: FtorComp'_def FtorComp_def MakeFtor_def)
qed

(* Step 2: Show that functors applied to arrows are distributed over dom and cod of arrow *)
lemma FtorComp'FtorM:
  assumes "Functor F"
  and "Functor G"
  and "CatCod F = CatDom G"
  shows "FunctorM (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)"
proof (auto simp add: FunctorM_def IdFtor'PreFunctor assms FunctorM_axioms_def)
  {
    fix f X Y
    assume hi:"f maps\<^bsub>CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> X to Y"
    show "(G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f maps\<^bsub>CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) @@ X to (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) @@ Y"
      proof -
        have "CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) = CatCod (G)" using assms CodFtorComp by blast
        moreover have "f \<in> mor\<^bsub>CatDom (F)\<^esub>" using assms DomFtorComp hi by fastforce
        moreover have "(G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f \<in> mor\<^bsub>CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub>" using assms hi
          proof -
            have "F ## f \<in> mor\<^bsub>CatCod (F)\<^esub>" using assms by (meson Functor.FunctorCompPreserved calculation)
            moreover have "F ## f \<in> mor\<^bsub>CatDom (G)\<^esub>" using assms using calculation by auto
            moreover have "G ## (F ## f) \<in> mor\<^bsub>CatCod (G)\<^esub>" using assms by (simp add: Functor.FunctorCompPreserved calculation)
            moreover have "G ## (F ## f) \<in> mor\<^bsub>CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub>" using assms by (simp add: `CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) = CatCod G` calculation(3))
            moreover have "G ## (F ## f) = (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f" using assms by (simp add: FtorComp'_def FtorComp_def MakeFtorMor `f \<in> mor\<^bsub>CatDom F\<^esub>`)
            ultimately show ?thesis by simp
          qed
        moreover have "dom\<^bsub>CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> ((G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f) = (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) @@ X" using assms CodFtorComp
          by (smt Category.CatIdInMor Category.Cdom DomFtorComp FtorComp'PreFunctor FtorComp'_def FtorComp_def Functor.FunctorCompPreserved Functor.FunctorId3Dom Functor.select_convs(1) Functor.select_convs(3) MakeFtorMor MapsToE PreFunctor.CatCod PreFunctor.CatDom PreFunctor.FmToFo hi)
        moreover have "cod\<^bsub>CatCod (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub> ((G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f) = (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) @@ Y"
          by (smt Category.CatIdInMor Category.Ccod DomFtorComp FtorComp'PreFunctor FtorComp'_def FtorComp_def Functor.FunctorCompPreserved Functor.FunctorId3Cod Functor.select_convs(1) Functor.select_convs(3) MakeFtorMor MapsToE PreFunctor.CatCod PreFunctor.CatDom PreFunctor.FmToFo assms(1) assms(2) assms(3) calculation(1) hi)
        ultimately show ?thesis using assms hi by blast
      qed
  }
  show "PreFunctor (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)" using assms by (rule FtorComp'PreFunctor)
qed


value "{ undefined }"

lemma FtorCompElim:
  assumes Ftor_F: "Functor F"
  and     Ftor_G: "Functor G"
  and     CodDom_FG: "CatCod F = CatDom G"
  shows "(G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f = G ## F ## f"
unfolding Functor_def
proof -
  have "undefined \<notin> Mor (CatDom G)" using assms
    proof (intro notI)
      assume "undefined \<in> Mor (CatDom G)"
      show "False" sorry
    qed
  next {
    fix f
    assume hi: "f \<in> mor\<^bsub>CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub>"
    have "f \<in> mor\<^bsub>CatDom (F)\<^esub>" using assms DomFtorComp hi by fastforce
    moreover have "G ## (F ## f) = (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f" using assms by (simp add: FtorComp'_def FtorComp_def MakeFtorMor `f \<in> mor\<^bsub>CatDom F\<^esub>`)
  }
  next {
    fix f
    assume hi: "f \<notin> mor\<^bsub>CatDom (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)\<^esub>"
    have "f \<notin> mor\<^bsub>CatDom (F)\<^esub>" using assms DomFtorComp hi by fastforce
    moreover have "G ## (F ## f) = (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## f" using assms hi
      proof -
        

      sorry
  }
  then show ?thesis (*  by (metis (no_types, lifting) FtorComp'_def FtorComp_def Functor.select_convs(1) Functor.select_convs(3) MakeFtorMor MakeFtor_def) *)
qed

(* Step 3 : Final gather *)
theorem FtorCompositionFtor: 
  assumes Ftor_F: "Functor F"
  and     Ftor_G: "Functor G"
  and     CodDom_FG: "CatCod F = CatDom G"
  shows "Functor (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)"
unfolding Functor_def
proof -
  have "FunctorM (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)" using assms by (rule FtorComp'FtorM)
  moreover have "FunctorExt (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F)" using assms
    proof - (* (auto simp add: FunctorExt_def)  *)
      (* have FunctorMapExt_F: "(MapM F) \<in> extensional (Mor (CatDom F))"
        using Ftor_F unfolding Functor_def by (simp add: FunctorExt.FunctorMapExt) *)
      have "\<forall>m. m \<notin> (Mor (CatDom F)) \<longrightarrow> (MapM F) m = undefined"
        using Ftor_F unfolding Functor_def (* by (meson FunctorExt.FunctorMapExt extensional_arb) *)
      have "undefined \<notin> Mor (CatDom G)"
        sorry
      have "\<forall>m. (G \<circ>\<^sub>F\<^sub>t\<^sub>o\<^sub>r F) ## m = G ## F ## m" using assms unfolding FtorComp using assms FtorComp'_def FtorComp_def MakeFtorMor sledgehamme
      moreover have FunctorMapExt_G: "(MapM G) \<in> extensional (Mor (CatDom G))"
        using Ftor_G unfolding Functor_def by (simp add: FunctorExt.FunctorMapExt)
      ultimately show ?thesis unfolding FtorComp_def sledgehamme
qed

end