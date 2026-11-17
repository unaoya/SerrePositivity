module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointCosliceFamilyHomotopyNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeLeg
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderMap
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.ExtOne
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.FunctorCategory
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointCosliceFamilyHomotopy
/-! 同じUnderのcoslice円柱は元の通常自然変換のnerveの全円柱である。 -/

@[expose] public section
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

private def underUnit {C : Type u} [Category.{u} C] (c : C) :
    (Functor.const (Under c)).obj c ⟶ Under.forget c where
  app x := x.hom
  naturality {_ _} f := by simpa using (Under.w f).symm
private lemma interval_one_cases (t : (Δ[1] : SSet.{u}) _⦋1⦌) :
    t = (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 0) ∨
      t = stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) ∨
        t = (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 1) := by
  by_cases h0 : (t 0).val = 0
  · by_cases h1 : (t 1).val = 0
    · left
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      fin_cases i <;> assumption
    · right; left
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      fin_cases i
      · exact h0
      · have h := (t 1).isLt
        change (t 1).val = 1
        omega
  · right; right
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have h := (t i).isLt
    have hm : (t 0).val ≤ (t i).val :=
      (stdSimplex.objEquiv t).toOrderHom.monotone (Fin.zero_le i)
    change (t i).val = 1
    omega
private lemma leftPrism_mixed {A : SSet.{u}} (σ : A _⦋1⦌) :
    (leftMappingSpacePrism A).app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), σ) =
      Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
        (stdSimplex.obj₀Equiv.symm 0) (A.δ 0 σ) := by
  change (joinCylinderMap (Δ[0] : SSet.{u}) A).app (Opposite.op ⦋1⦌)
    (((Δ[0] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 0),
      stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)), σ) = _
  have hcut : ((joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))).1 = (1 : Fin 3) := by
    apply Fin.ext
    exact Join.pullCut_id 1 (by decide)
  rw [joinCylinderMap_app]
  generalize hs : (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋1⦌)
    (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = z at *
  rcases z with ⟨l, a, b⟩
  change l = (1 : Fin 3) at hcut
  subst l
  dsimp only
  refine Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · apply stdSimplex.ext
    intro i
    exact Fin.ext (by omega)
  · have he : SimplexCategory.mkHom (Join.suffixIncl 2 1 (by decide)) =
        SimplexCategory.δ (0 : Fin 2) := by
      ext i
      fin_cases i
      rfl
    change A.map (SimplexCategory.mkHom (Join.suffixIncl 2 1 (by decide))).op σ = _
    rw [he]
    rfl
private lemma underUnitCylinder_mixed {C : Type u} [Category.{u} C] (c : C)
    (σ : (nerve (Under c)) _⦋1⦌) :
    (nerveNatTransHomotopy (underUnit c)).h.app (Opposite.op ⦋1⦌)
      (σ, stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = ComposableArrows.mk₁ (σ.obj 1).hom := by
  let z : (nerve ((Under c) × ((Under c) ⥤ C))) _⦋1⦌ :=
    σ.prod' (ComposableArrows.mk₁ (underUnit c))
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso_uncurry
      (Under c) C) (Opposite.op ⦋1⦌)) z
  change (((SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso
    (Under c) C).hom.app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ (underUnit c))).app (Opposite.op ⦋1⦌)
        (𝟙 (Opposite.op ⦋1⦌))) σ = _ at h
  change (((SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso
    (Under c) C).hom.app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ (underUnit c))).app (Opposite.op ⦋1⦌)
        (𝟙 (Opposite.op ⦋1⦌))) σ = _
  refine h.trans ?_
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (𝟙 c) ≫ (σ.obj 1).hom = _
  exact Category.id_comp _
private lemma underCosliceCylinder {C : Type u} [Category.{u} C] (c : C) :
    (pointCosliceFamilyHomotopy (nerveUnderMap c)).h =
      (nerveNatTransHomotopy (underUnit c)).h := by
  apply nerve_hom_ext_one
  rintro ⟨σ, t⟩
  rcases interval_one_cases t with ht | ht | ht <;> subst t
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (pointCosliceFamilyHomotopy (nerveUnderMap c)).h₀ (Opposite.op ⦋1⦌)) σ
    have h' := ConcreteCategory.congr_hom (NatTrans.congr_app
      (nerveNatTransHomotopy (underUnit c)).h₀ (Opposite.op ⦋1⦌)) σ
    exact h.trans h'.symm
  · rw [underUnitCylinder_mixed]
    change (sliceUnderUncurry (nerveUnderMap c)).app (Opposite.op ⦋1⦌)
      ((leftMappingSpacePrism (nerve (Under c))).app (Opposite.op ⦋1⦌)
        (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), σ)) = _
    rw [leftPrism_mixed]
    change sliceUnderUncurryApp (nerveUnderMap c) 1
      (Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
        (stdSimplex.obj₀Equiv.symm 0) ((nerve (Under c)).δ 0 σ)) =
      ComposableArrows.mk₁ (σ.obj 1).hom
    rw [sliceUnderUncurryApp_mkOfSum]
    dsimp only [sliceUnderEval, nerveUnderMap, nerveUnderSimplex]
    have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) := by
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    rw [hp]
    change ((pointJoinStdSimplexIso.{u} 0).hom ≫
      (SSet.yonedaEquiv (X := nerve C)).symm
        (nerveUnderChain c ((nerve (Under c)).δ 0 σ))).app (Opposite.op ⦋1⦌)
        (Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
          (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))
          (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) = _
    rw [NatTrans.comp_app_apply,
      SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pointJoinStdSimplexIso_zero_leg]
    have hy := SSet.yonedaEquiv_symm_app_objEquiv_symm (X := nerve C)
      (nerveUnderChain c ((nerve (Under c)).δ 0 σ)) (𝟙 ⦋1⦌)
    have hy' : ((SSet.yonedaEquiv (X := nerve C)).symm
        (nerveUnderChain c ((nerve (Under c)).δ 0 σ))).app (Opposite.op ⦋1⦌)
          (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
        nerveUnderChain c ((nerve (Under c)).δ 0 σ) := by
      have hid : (nerve C).map (𝟙 ⦋1⦌).op =
          𝟙 ((nerve C).obj (Opposite.op ⦋1⦌)) :=
        (congrArg (nerve C).map (show (𝟙 ⦋1⦌).op = 𝟙 (Opposite.op ⦋1⦌) from op_id)).trans ((nerve C).map_id _)
      exact hy.trans (ConcreteCategory.congr_hom hid _)
    refine hy'.trans ?_
    refine ComposableArrows.ext₁ rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (pointCosliceFamilyHomotopy (nerveUnderMap c)).h₁ (Opposite.op ⦋1⦌)) σ
    have h' := ConcreteCategory.congr_hom (NatTrans.congr_app
      (nerveNatTransHomotopy (underUnit c)).h₁ (Opposite.op ⦋1⦌)) σ
    have hp := ConcreteCategory.congr_hom (NatTrans.congr_app
      (nerveUnderMap_projection c) (Opposite.op ⦋1⦌)) σ
    exact h.trans (hp.trans h'.symm)

/-- 任意の元の自然変換の全円柱を、同じUnderのcoslice表示から厳密に回収する。 -/
lemma nerveUnderLift_pointCosliceFamilyHomotopy {I C : Type u} [Category.{u} I]
    [Category.{u} C] {c : C} {V : I ⥤ C} (η : (Functor.const I).obj c ⟶ V) :
    (pointCosliceFamilyHomotopy (nerveMap (Under.lift V η) ≫ nerveUnderMap c)).h =
      (nerveNatTransHomotopy η).h := by
  rw [← pointCosliceFamilyHomotopy_precomp_h (nerveVertex c)
    (nerveMap (Under.lift V η) ≫ nerveUnderMap c)]
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
    pointCosliceFamilyHomotopy_precomp_h, underCosliceCylinder,
    nerveNatTransHomotopy_whiskerLeft]
  rfl

/-- 同じ円柱を指定モデル源へ送り、元の全関手圏の射の像を照合する。 -/
lemma nerveUnderLift_pointCosliceFamilyHomotopy_postcomp_arrow {I C : Type u}
    [Category.{u} I] [Category.{u} C] {c : C} {V : I ⥤ C}
    (η : (Functor.const I).obj c ⟶ V) {D : SSet.{u}} (F : nerve C ⟶ D) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (pointCosliceFamilyHomotopy
        (nerveMap (Under.lift V η) ≫ nerveUnderMap c)) F))) =
      Arrow.mk ((hoFunctor.map ((ihom (nerve I)).map F)).toFunctor.map
        (nerveNatTransHom η)) := by
  calc
    _ = Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (nerveNatTransHomotopy η) F))) := by
      apply Truncated.HomotopyCategory.congr_arrowMk_homMk
      change SSet.yonedaEquiv (curry ((pointCosliceFamilyHomotopy
          (nerveMap (Under.lift V η) ≫ nerveUnderMap c)).h ≫ F)) =
        SSet.yonedaEquiv (curry ((nerveNatTransHomotopy η).h ≫ F))
      rw [nerveUnderLift_pointCosliceFamilyHomotopy]
    _ = _ := congrArg Arrow.mk ((functorHomotopyPostcomp_hom
      (nerveNatTransHomotopy η) F).trans (congrArg
        ((hoFunctor.map ((ihom (nerve I)).map F)).toFunctor.map)
          (nerveNatTransHomotopy_hom η)))
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
end
