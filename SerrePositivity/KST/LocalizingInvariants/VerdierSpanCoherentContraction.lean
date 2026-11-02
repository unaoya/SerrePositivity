module

public import SerrePositivity.KST.LocalizingInvariants.VerdierFractionComparison
public import SerrePositivity.KST.Fibration.WeakSpanKanQuotientFamilyIdentity
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMinimum
public import SerrePositivity.InfinityCategories.F1B.Diagrams.IntervalMaximum
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
public import SerrePositivity.KST.LocalizingInvariants.IntervalMarkedEdges
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor
public import SerrePositivity.KST.Fibration.IdentityMarkedSpan
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorCompositionRestriction
public import SerrePositivity.InfinityCategories.F1.Joins.HomotopyConeRealization
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFamilyInvariance
public import SerrePositivity.KST.Fibration.FractionFamilyCoslice
public import SerrePositivity.KST.Fibration.PointSourceCosliceFiber
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFamilySquareInverse
public import SerrePositivity.KST.Fibration.PointSourceFatRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationInitialSpan
public import SerrePositivity.InfinityCategories.F1.Joins.CoslicePostCoordinates
public import SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionEvaluation
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationCoslicePointUniqueness
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorFiberHom
public import SerrePositivity.KST.Fibration.CoslicePointFamilyAt
public import SerrePositivity.KST.Fibration.WeakQuotientCosliceUnit
public import SerrePositivity.KST.Fibration.WeakCosliceScaffoldTriangle
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.Core.EquivalenceTwoOfSix
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber
public import SerrePositivity.InfinityCategories.F2.Compact.SpaceEdgeValueEquivalence

/-!
概要：一般 Verdier 分数の全族に対して、分母 roof からの二つの実変形を保持する。
方針：元の span の第一辺を保つ変形と、分母による恒等 span への変形を用いる。
規約：元の実全族単位・全 fiber 回収と指定恒等点照合を適用する。π₀ だけでは代用しない。
使われ方：Sp-6 s4 の一般 Verdier 分数比較の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

private def denominatorSpanCollapse : (horn 2 0 : SSet.{u}) ⟶ horn 2 0 :=
  horn₂₀.isPushout.desc horn₂₀.ι₀₁
    (SSet.const (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) (by
      apply SSet.yonedaEquiv.injective
      decide)

private lemma denominatorSpanCollapse_left :
    (horn₂₀.ι₀₁ : (Δ[1] : SSet.{u}) ⟶ horn 2 0) ≫ denominatorSpanCollapse =
      horn₂₀.ι₀₁ := horn₂₀.isPushout.inl_desc _ _ _

private lemma denominatorSpanCollapse_right :
    (horn₂₀.ι₀₂ : (Δ[1] : SSet.{u}) ⟶ horn 2 0) ≫ denominatorSpanCollapse =
      SSet.const (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := horn₂₀.isPushout.inr_desc _ _ _

private lemma denominatorSpanRightExpansion_comm :
    curry (fst (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    curry (intervalMinimum ≫ horn₂₀.ι₀₂) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  simp only [curry_evaluateFunctorAt_interval, ← Category.assoc,
    intervalMinimum_first_zero, SSet.const_comp]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro v
  apply Subtype.ext
  rfl

private def denominatorSpanRightExpansion :
    (Δ[1] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj (horn 2 0) :=
  stable_spanFamilyOfArrows
    (curry (fst (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
    (curry (intervalMinimum ≫ horn₂₀.ι₀₂)) denominatorSpanRightExpansion_comm

private lemma denominatorCurry_zero {X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (curry H).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      functorVertex (SSet.ι₀ ≫ H) := by
  have hh := functorVertex_uncurry_zero (SSet.yonedaEquiv (curry H))
  rw [Equiv.symm_apply_apply, uncurry_curry] at hh
  exact (intervalMap_source (curry H)).symm.trans hh.symm

private lemma denominatorCurry_one {X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (curry H).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      functorVertex (SSet.ι₁ ≫ H) := by
  have hh := functorVertex_uncurry_one (SSet.yonedaEquiv (curry H))
  rw [Equiv.symm_apply_apply, uncurry_curry] at hh
  exact (intervalMap_target (curry H)).symm.trans hh.symm

private lemma denominatorSpanRightExpansion_zero :
    denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        functorVertex (denominatorSpanCollapse : (horn 2 0 : SSet.{u}) ⟶ _) := by
  obtain ⟨F, hF⟩ := (functorVertexEquiv (horn 2 0 : SSet.{u}) _).surjective
    (denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
  change functorVertex F = _ at hF
  rw [← hF]
  apply congrArg functorVertex
  apply horn₂₀.isPushout.hom_ext
  · apply functorVertex_injective
    have hl := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (stable_spanFamilyOfArrows_left
        (curry (fst (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
        (curry (intervalMinimum ≫ horn₂₀.ι₀₂)) denominatorSpanRightExpansion_comm)
    change ((pre horn₂₀.ι₀₁).app (horn 2 0 : SSet.{u})).app (Opposite.op ⦋0⦌)
      (denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _ at hl
    rw [← hF, denominatorCurry_zero] at hl
    rw [denominatorSpanCollapse_left]
    exact hl.trans (congrArg functorVertex (by
      change SSet.ι₀ ≫ fst (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁ = horn₂₀.ι₀₁
      rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]))
  · apply functorVertex_injective
    have hr := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (stable_spanFamilyOfArrows_right
        (curry (fst (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
        (curry (intervalMinimum ≫ horn₂₀.ι₀₂)) denominatorSpanRightExpansion_comm)
    change ((pre horn₂₀.ι₀₂).app (horn 2 0 : SSet.{u})).app (Opposite.op ⦋0⦌)
      (denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _ at hr
    rw [← hF, denominatorCurry_zero] at hr
    change functorVertex (horn₂₀.ι₀₂ ≫ F) = _ at hr
    rw [← Category.assoc, intervalMinimum_second_zero, SSet.const_comp] at hr
    rw [denominatorSpanCollapse_right]
    exact hr.trans (congrArg functorVertex (by
      congr 1))

private lemma denominatorSpanRightExpansion_one :
    denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        functorVertex (𝟙 (horn 2 0 : SSet.{u})) := by
  obtain ⟨F, hF⟩ := (functorVertexEquiv (horn 2 0 : SSet.{u}) _).surjective
    (denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  change functorVertex F = _ at hF
  rw [← hF]
  apply congrArg functorVertex
  apply horn₂₀.isPushout.hom_ext
  · apply functorVertex_injective
    have hl := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (stable_spanFamilyOfArrows_left
        (curry (fst (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
        (curry (intervalMinimum ≫ horn₂₀.ι₀₂)) denominatorSpanRightExpansion_comm)
    change ((pre horn₂₀.ι₀₁).app (horn 2 0 : SSet.{u})).app (Opposite.op ⦋0⦌)
      (denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _ at hl
    rw [← hF, denominatorCurry_one] at hl
    rw [Category.comp_id]
    exact hl.trans (congrArg functorVertex (by
      change SSet.ι₁ ≫ fst (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁ = horn₂₀.ι₀₁
      rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]))
  · apply functorVertex_injective
    have hr := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (stable_spanFamilyOfArrows_right
        (curry (fst (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
        (curry (intervalMinimum ≫ horn₂₀.ι₀₂)) denominatorSpanRightExpansion_comm)
    change ((pre horn₂₀.ι₀₂).app (horn 2 0 : SSet.{u})).app (Opposite.op ⦋0⦌)
      (denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _ at hr
    rw [← hF, denominatorCurry_one] at hr
    change functorVertex (horn₂₀.ι₀₂ ≫ F) = _ at hr
    rw [← Category.assoc, intervalMinimum_second_one, Category.id_comp] at hr
    simpa only [Category.comp_id] using hr

private lemma denominatorSpanLeftContraction_comm :
    curry (F1B.intervalMaximum ≫ (horn₂₀.ι₀₁ : (Δ[1] : SSet.{u}) ⟶ _)) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    curry (snd (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  simp only [curry_evaluateFunctorAt_interval, ← Category.assoc,
    F1B.intervalMaximum_first_zero, Category.id_comp]
  rfl

private def denominatorSpanLeftContraction :
    (Δ[1] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj (horn 2 0) :=
  stable_spanFamilyOfArrows
    (curry (F1B.intervalMaximum ≫ horn₂₀.ι₀₁))
    (curry (snd (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
    denominatorSpanLeftContraction_comm

private lemma denominatorSpanLeftContraction_zero :
    denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        functorVertex (denominatorSpanCollapse : (horn 2 0 : SSet.{u}) ⟶ _) := by
  obtain ⟨F, hF⟩ := (functorVertexEquiv (horn 2 0 : SSet.{u}) _).surjective
    (denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
  change functorVertex F = _ at hF
  rw [← hF]
  apply congrArg functorVertex
  apply horn₂₀.isPushout.hom_ext
  · apply functorVertex_injective
    have hl := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (stable_spanFamilyOfArrows_left
        (curry (F1B.intervalMaximum ≫ horn₂₀.ι₀₁))
        (curry (snd (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
        denominatorSpanLeftContraction_comm)
    change ((pre horn₂₀.ι₀₁).app (horn 2 0 : SSet.{u})).app (Opposite.op ⦋0⦌)
      (denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _ at hl
    rw [← hF, denominatorCurry_zero] at hl
    change functorVertex (horn₂₀.ι₀₁ ≫ F) = _ at hl
    rw [← Category.assoc, F1B.intervalMaximum_second_zero, Category.id_comp] at hl
    simpa only [denominatorSpanCollapse_left] using hl
  · apply functorVertex_injective
    have hr := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (stable_spanFamilyOfArrows_right
        (curry (F1B.intervalMaximum ≫ horn₂₀.ι₀₁))
        (curry (snd (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
        denominatorSpanLeftContraction_comm)
    change ((pre horn₂₀.ι₀₂).app (horn 2 0 : SSet.{u})).app (Opposite.op ⦋0⦌)
      (denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _ at hr
    rw [← hF, denominatorCurry_zero] at hr
    change functorVertex (horn₂₀.ι₀₂ ≫ F) = _ at hr
    rw [← Category.assoc, SSet.ι₀_snd, SSet.const_comp] at hr
    simpa only [denominatorSpanCollapse_right] using hr

private lemma denominatorSpanLeftContraction_one :
    denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        functorVertex (SSet.const (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) : (horn 2 0 : SSet.{u}) ⟶ _) := by
  obtain ⟨F, hF⟩ := (functorVertexEquiv (horn 2 0 : SSet.{u}) _).surjective
    (denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  change functorVertex F = _ at hF
  rw [← hF]
  apply congrArg functorVertex
  apply horn₂₀.isPushout.hom_ext
  · apply functorVertex_injective
    have hl := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (stable_spanFamilyOfArrows_left
        (curry (F1B.intervalMaximum ≫ horn₂₀.ι₀₁))
        (curry (snd (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
        denominatorSpanLeftContraction_comm)
    change ((pre horn₂₀.ι₀₁).app (horn 2 0 : SSet.{u})).app (Opposite.op ⦋0⦌)
      (denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _ at hl
    rw [← hF, denominatorCurry_one] at hl
    change functorVertex (horn₂₀.ι₀₁ ≫ F) = _ at hl
    rw [← Category.assoc, F1B.intervalMaximum_second_one, SSet.const_comp] at hl
    simpa only [SSet.comp_const] using hl
  · apply functorVertex_injective
    have hr := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (stable_spanFamilyOfArrows_right
        (curry (F1B.intervalMaximum ≫ horn₂₀.ι₀₁))
        (curry (snd (Δ[1] : SSet.{u}) Δ[1] ≫ horn₂₀.ι₀₁))
        denominatorSpanLeftContraction_comm)
    change ((pre horn₂₀.ι₀₂).app (horn 2 0 : SSet.{u})).app (Opposite.op ⦋0⦌)
      (denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _ at hr
    rw [← hF, denominatorCurry_one] at hr
    change functorVertex (horn₂₀.ι₀₂ ≫ F) = _ at hr
    rw [← Category.assoc, SSet.ι₁_snd, SSet.const_comp] at hr
    simpa only [SSet.comp_const] using hr

/-- 全 span をパラメーターに保った実変形。時刻は第二因子。 -/
private def verdierSpanRightExpansion (B : StableCategory.{u}) :
    SSet.Homotopy ((pre denominatorSpanCollapse).app B.obj)
      (𝟙 ((ihom (horn 2 0 : SSet.{u})).obj B.obj)) := by
  let F := denominatorSpanRightExpansion ≫
    functorPrecompositionMap (horn 2 0 : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj
  refine simplicialHomotopyOfFunctorEdge ⟨SSet.yonedaEquiv F, ?_, ?_⟩
  · refine (intervalMap_source F).trans ?_
    change (functorPrecompositionMap (horn 2 0 : SSet.{u}) _ B.obj).app
      (Opposite.op ⦋0⦌) (denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
    rw [denominatorSpanRightExpansion_zero, functorPrecompositionMap_vertex]
  · refine (intervalMap_target F).trans ?_
    change (functorPrecompositionMap (horn 2 0 : SSet.{u}) _ B.obj).app
      (Opposite.op ⦋0⦌) (denominatorSpanRightExpansion.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
    rw [denominatorSpanRightExpansion_one, functorPrecompositionMap_vertex,
      pre_id, NatTrans.id_app]

/-- 全 span を、元の第一終点の恒等 span へ分母に沿って変形する。 -/
private def verdierSpanLeftContraction (B : StableCategory.{u}) :
    SSet.Homotopy ((pre denominatorSpanCollapse).app B.obj)
      ((pre (SSet.const (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
          (horn 2 0 : SSet.{u}) ⟶ _)).app B.obj) := by
  let F := denominatorSpanLeftContraction ≫
    functorPrecompositionMap (horn 2 0 : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj
  refine simplicialHomotopyOfFunctorEdge ⟨SSet.yonedaEquiv F, ?_, ?_⟩
  · refine (intervalMap_source F).trans ?_
    change (functorPrecompositionMap (horn 2 0 : SSet.{u}) _ B.obj).app
      (Opposite.op ⦋0⦌) (denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
    rw [denominatorSpanLeftContraction_zero, functorPrecompositionMap_vertex]
  · refine (intervalMap_target F).trans ?_
    change (functorPrecompositionMap (horn 2 0 : SSet.{u}) _ B.obj).app
      (Opposite.op ⦋0⦌) (denominatorSpanLeftContraction.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
    rw [denominatorSpanLeftContraction_one, functorPrecompositionMap_vertex]

private lemma verdierSpanLeftRestriction_natural (B : StableCategory.{u}) :
    functorPrecompositionMap (horn 2 0 : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj ≫
      (ihom ((ihom (horn 2 0 : SSet.{u})).obj B.obj)).map
        ((pre horn₂₀.ι₀₁).app B.obj) =
    (pre horn₂₀.ι₀₁).app (horn 2 0 : SSet.{u}) ≫
      functorPrecompositionMap (Δ[1] : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj := by
  rfl

private lemma denominatorSpanRightExpansion_left :
    (denominatorSpanRightExpansion : (Δ[1] : SSet.{u}) ⟶ _) ≫
      (pre horn₂₀.ι₀₁).app (horn 2 0 : SSet.{u}) =
        SSet.const (functorVertex horn₂₀.ι₀₁) := by
  rw [denominatorSpanRightExpansion, stable_spanFamilyOfArrows_left]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_const_functorVertex]

private lemma verdierSpanRightExpansion_left (B : StableCategory.{u}) :
    (verdierSpanRightExpansion B).h ≫ (pre horn₂₀.ι₀₁).app B.obj =
      fst ((ihom (horn 2 0 : SSet.{u})).obj B.obj) Δ[1] ≫
        (pre horn₂₀.ι₀₁).app B.obj := by
  let F := denominatorSpanRightExpansion ≫
    functorPrecompositionMap (horn 2 0 : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv F)) ≫
    (pre horn₂₀.ι₀₁).app B.obj = _
  rw [Equiv.symm_apply_apply, ← uncurry_natural_right]
  have he : F ≫ (ihom ((ihom (horn 2 0 : SSet.{u})).obj B.obj)).map
      ((pre horn₂₀.ι₀₁).app B.obj) =
        SSet.const (functorVertex ((pre horn₂₀.ι₀₁).app B.obj)) := by
    dsimp only [F]
    rw [Category.assoc, verdierSpanLeftRestriction_natural, ← Category.assoc,
      denominatorSpanRightExpansion_left, SSet.const_comp, functorPrecompositionMap_vertex]
  rw [he, uncurry_const_functorVertex]

private def verdierMarkedRightExpansionRaw {A B : StableCategory.{u}} (i : ExactMap A B) :
    markedSpans B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) ⊗
      (Δ[1] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj B.obj :=
  (markedSpanInclusion B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) ▷
    (Δ[1] : SSet.{u})) ≫ (verdierSpanRightExpansion B).h

private def verdierMarkedRightExpansion {A B : StableCategory.{u}} (i : ExactMap A B) :
    markedSpans B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) ⊗
      (Δ[1] : SSet.{u}) ⟶
        markedSpans B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) :=
  fullSubcomplexLift _ (verdierMarkedRightExpansionRaw i) (by
    rintro ⟨v, t⟩
    have he := congrArg (fun F => F.app (Opposite.op ⦋0⦌) (v.val, t))
      (verdierSpanRightExpansion_left B)
    change ((pre horn₂₀.ι₀₁).app B.obj).app (Opposite.op ⦋0⦌)
      ((verdierSpanRightExpansion B).h.app (Opposite.op ⦋0⦌) (v.val, t)) =
        ((pre horn₂₀.ι₀₁).app B.obj).app (Opposite.op ⦋0⦌) v.val at he
    change spanLeftEdge ((verdierSpanRightExpansion B).h.app
      (Opposite.op ⦋0⦌) (v.val, t)) ∈ _
    unfold spanLeftEdge
    rw [he]
    exact fullSubcomplexOnVertices_vertex v)

private lemma verdierMarkedRightExpansion_inclusion {A B : StableCategory.{u}}
    (i : ExactMap A B) :
    verdierMarkedRightExpansion i ≫
      markedSpanInclusion B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) =
        verdierMarkedRightExpansionRaw i := fullSubcomplexLift_ι _ _ _

private lemma verdierMarkedRightExpansion_source {A B : StableCategory.{u}}
    (i : ExactMap A B) :
    verdierMarkedRightExpansion i ≫
      markedSpanSource B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) =
    fst (markedSpans B.obj (SerrePositivity.KST.Fibration.weakEquivalences i)) Δ[1] ≫
      markedSpanSource B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) := by
  unfold markedSpanSource
  rw [← Category.assoc, verdierMarkedRightExpansion_inclusion]
  dsimp only [verdierMarkedRightExpansionRaw]
  simp only [Category.assoc]
  rw [← Category.assoc (verdierSpanRightExpansion B).h,
    verdierSpanRightExpansion_left]
  rfl

private lemma verdierMarkedRightExpansion_one {A B : StableCategory.{u}}
    (i : ExactMap A B) :
    (SSet.ι₁ : markedSpans B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) ⟶ _) ≫
      verdierMarkedRightExpansion i = 𝟙 _ := by
  have : Mono (markedSpanInclusion B.obj
      (SerrePositivity.KST.Fibration.weakEquivalences i)) := by
    dsimp only [markedSpanInclusion]
    infer_instance
  apply (cancel_mono (markedSpanInclusion B.obj
    (SerrePositivity.KST.Fibration.weakEquivalences i))).mp
  rw [Category.assoc, verdierMarkedRightExpansion_inclusion, Category.id_comp]
  dsimp only [verdierMarkedRightExpansionRaw]
  have he : (SSet.ι₁ : markedSpans B.obj
      (SerrePositivity.KST.Fibration.weakEquivalences i) ⟶ _) ≫
      (markedSpanInclusion B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) ▷
        (Δ[1] : SSet.{u})) =
      markedSpanInclusion B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) ≫
        SSet.ι₁ := rfl
  rw [← Category.assoc, he, Category.assoc, (verdierSpanRightExpansion B).h₁,
    Category.comp_id]

private def verdierFixedSourceRightExpansion {A B : StableCategory.{u}}
    (i : ExactMap A B) (x : B.obj _⦋0⦌) :
    markedSpanFamily B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) x ⊗
      (Δ[1] : SSet.{u}) ⟶
        markedSpanFamily B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) x :=
  vertexFiberLift (markedSpanSource B.obj
    (SerrePositivity.KST.Fibration.weakEquivalences i)) x
      ((vertexFiberι (markedSpanSource B.obj
        (SerrePositivity.KST.Fibration.weakEquivalences i)) x ▷ (Δ[1] : SSet.{u})) ≫
        verdierMarkedRightExpansion i) (by
    rw [Category.assoc, verdierMarkedRightExpansion_source]
    have he : (vertexFiberι (markedSpanSource B.obj
        (SerrePositivity.KST.Fibration.weakEquivalences i)) x ▷ (Δ[1] : SSet.{u})) ≫
        fst (markedSpans B.obj (SerrePositivity.KST.Fibration.weakEquivalences i)) Δ[1] =
      fst (markedSpanFamily B.obj (SerrePositivity.KST.Fibration.weakEquivalences i) x)
        Δ[1] ≫ vertexFiberι (markedSpanSource B.obj
          (SerrePositivity.KST.Fibration.weakEquivalences i)) x := rfl
    rw [← Category.assoc, he, Category.assoc, vertexFiberι_comp, SSet.comp_const])

private lemma verdierFixedSourceRightExpansion_inclusion {A B : StableCategory.{u}}
    (i : ExactMap A B) (x : B.obj _⦋0⦌) :
    verdierFixedSourceRightExpansion i x ≫ vertexFiberι (markedSpanSource B.obj
      (SerrePositivity.KST.Fibration.weakEquivalences i)) x =
    (vertexFiberι (markedSpanSource B.obj
      (SerrePositivity.KST.Fibration.weakEquivalences i)) x ▷ (Δ[1] : SSet.{u})) ≫
        verdierMarkedRightExpansion i := vertexFiberLift_ι _ _ _ _

private lemma verdierFixedSourceRightExpansion_one {A B : StableCategory.{u}}
    (i : ExactMap A B) (x : B.obj _⦋0⦌) :
    (SSet.ι₁ : markedSpanFamily B.obj
      (SerrePositivity.KST.Fibration.weakEquivalences i) x ⟶ _) ≫
        verdierFixedSourceRightExpansion i x = 𝟙 _ := by
  apply vertexFiber_hom_ext (markedSpanSource B.obj
    (SerrePositivity.KST.Fibration.weakEquivalences i)) x
  rw [Category.assoc, verdierFixedSourceRightExpansion_inclusion, Category.id_comp]
  have he : (SSet.ι₁ : markedSpanFamily B.obj
      (SerrePositivity.KST.Fibration.weakEquivalences i) x ⟶ _) ≫
      (vertexFiberι (markedSpanSource B.obj
        (SerrePositivity.KST.Fibration.weakEquivalences i)) x ▷ (Δ[1] : SSet.{u})) =
      vertexFiberι (markedSpanSource B.obj
        (SerrePositivity.KST.Fibration.weakEquivalences i)) x ≫ SSet.ι₁ := rfl
  rw [← Category.assoc, he, Category.assoc, verdierMarkedRightExpansion_one,
    Category.comp_id]

private lemma denominatorSpanLeftContraction_source :
    (denominatorSpanLeftContraction : (Δ[1] : SSet.{u}) ⟶ _) ≫
      evaluateFunctorAt (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
      SSet.const (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  change denominatorSpanLeftContraction ≫
    (pre horn₂₀.ι₀₁).app (horn 2 0 : SSet.{u}) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  rw [← Category.assoc, denominatorSpanLeftContraction, stable_spanFamilyOfArrows_left,
    curry_evaluateFunctorAt_interval, ← Category.assoc,
    F1B.intervalMaximum_first_one, SSet.const_comp]

private def verdierSpanSourceEvaluation (B : StableCategory.{u}) :
    (horn 2 0 : SSet.{u}) ⟶
      (ihom ((ihom (horn 2 0 : SSet.{u})).obj B.obj)).obj B.obj :=
  internalHomFlipHomEquiv ((ihom (horn 2 0 : SSet.{u})).obj B.obj)
    (horn 2 0 : SSet.{u}) B.obj (𝟙 _)

private lemma verdierSpanSourceEvaluation_vertex (B : StableCategory.{u})
    (v : (horn 2 0 : SSet.{u}) _⦋0⦌) :
    (verdierSpanSourceEvaluation B).app (Opposite.op ⦋0⦌) v =
      functorVertex (evaluateFunctorAt (Y := B.obj) v) := by
  rw [verdierSpanSourceEvaluation, internalHomFlipHomEquiv_app_zero, Category.id_comp]

private lemma verdierSpanSourceRestriction_natural (B : StableCategory.{u})
    (v : (horn 2 0 : SSet.{u}) _⦋0⦌) :
    functorPrecompositionMap (horn 2 0 : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj ≫
      (ihom ((ihom (horn 2 0 : SSet.{u})).obj B.obj)).map
        (evaluateFunctorAt v) =
    evaluateFunctorAt v ≫
        verdierSpanSourceEvaluation B := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro G
  change G.app d (𝟙 d) (F.app d (α ≫ 𝟙 d)
      ((horn 2 0 : SSet.{u}).map (𝟙 d) (PinchedHom.constant v d.unop.len))) =
    (((ihom (horn 2 0 : SSet.{u})).obj B.obj).map (𝟙 d) G).app d (𝟙 d)
      ((horn 2 0 : SSet.{u}).map α
        (F.app (Opposite.op ⦋n⦌) (𝟙 _) (PinchedHom.constant v n)))
  rw [Category.comp_id, CategoryTheory.Functor.map_id_apply,
    CategoryTheory.Functor.map_id_apply]
  apply congrArg (fun z => G.app d (𝟙 d) z)
  have hh := ConcreteCategory.congr_hom (F.naturality α (𝟙 _))
    (PinchedHom.constant v n)
  change F.app d ((𝟙 (Opposite.op ⦋n⦌)) ≫ α)
      ((horn 2 0 : SSet.{u}).map α (PinchedHom.constant v n)) =
    (horn 2 0 : SSet.{u}).map α
      (F.app (Opposite.op ⦋n⦌) (𝟙 _) (PinchedHom.constant v n)) at hh
  have hc : (horn 2 0 : SSet.{u}).map α (PinchedHom.constant v n) =
      PinchedHom.constant v d.unop.len := PinchedHom.constant_pullback v α.unop
  rw [Category.id_comp, hc] at hh
  exact hh

private lemma verdierSpanLeftContraction_source (B : StableCategory.{u}) :
    (verdierSpanLeftContraction B).h ≫
      evaluateFunctorAt (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
    fst ((ihom (horn 2 0 : SSet.{u})).obj B.obj) Δ[1] ≫
      evaluateFunctorAt (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  let F := denominatorSpanLeftContraction ≫
    functorPrecompositionMap (horn 2 0 : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv F)) ≫ _ = _
  rw [Equiv.symm_apply_apply, ← uncurry_natural_right]
  have he : F ≫ (ihom ((ihom (horn 2 0 : SSet.{u})).obj B.obj)).map
      (evaluateFunctorAt (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
    SSet.const (functorVertex (evaluateFunctorAt (Y := B.obj)
      (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) := by
    dsimp only [F]
    rw [Category.assoc, verdierSpanSourceRestriction_natural, ← Category.assoc,
      denominatorSpanLeftContraction_source, SSet.const_comp,
      verdierSpanSourceEvaluation_vertex]
  rw [he, uncurry_const_functorVertex]

private lemma denominatorSpanCollapse_preserves_left (B : StableCategory.{u}) :
    (pre denominatorSpanCollapse).app B.obj ≫ (pre horn₂₀.ι₀₁).app B.obj =
      (pre horn₂₀.ι₀₁).app B.obj := by
  rw [← NatTrans.comp_app, ← pre_map, denominatorSpanCollapse_left]

private def verdierMarkedLeftContractionRaw {A B : StableCategory.{u}} (i : ExactMap A B) :
    markedSpans B.obj (weakEquivalences i) ⊗ (Δ[1] : SSet.{u}) ⟶
      (ihom (horn 2 0 : SSet.{u})).obj B.obj :=
  (markedSpanInclusion B.obj (weakEquivalences i) ▷ (Δ[1] : SSet.{u})) ≫
    (verdierSpanLeftContraction B).h

private def verdierMarkedLeftContraction {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q) :
    markedSpans B.obj (weakEquivalences i) ⊗ (Δ[1] : SSet.{u}) ⟶
      markedSpans B.obj (weakEquivalences i) :=
  fullSubcomplexLift _ (verdierMarkedLeftContractionRaw i) (by
    rintro ⟨v, t⟩
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
    change spanLeftEdge ((verdierSpanLeftContraction B).h.app (Opposite.op ⦋0⦌)
      (v.val, stdSimplex.obj₀Equiv.symm j)) ∈ weakEquivalences i
    fin_cases j
    · change spanLeftEdge ((verdierSpanLeftContraction B).h.app (Opposite.op ⦋0⦌)
        (v.val, stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ∈ _
      have he := congrArg (fun F => F.app (Opposite.op ⦋0⦌) v.val)
        (verdierSpanLeftContraction B).h₀
      change (verdierSpanLeftContraction B).h.app (Opposite.op ⦋0⦌)
        (v.val, stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        ((pre denominatorSpanCollapse).app B.obj).app (Opposite.op ⦋0⦌) v.val at he
      rw [he]
      have hl := congrArg (fun F => F.app (Opposite.op ⦋0⦌) v.val)
        (denominatorSpanCollapse_preserves_left B)
      change ((pre horn₂₀.ι₀₁).app B.obj).app (Opposite.op ⦋0⦌)
        (((pre denominatorSpanCollapse).app B.obj).app (Opposite.op ⦋0⦌) v.val) =
        ((pre horn₂₀.ι₀₁).app B.obj).app (Opposite.op ⦋0⦌) v.val at hl
      unfold spanLeftEdge
      rw [hl]
      exact fullSubcomplexOnVertices_vertex v
    · change spanLeftEdge ((verdierSpanLeftContraction B).h.app (Opposite.op ⦋0⦌)
        (v.val, stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ∈ _
      have he := congrArg (fun F => F.app (Opposite.op ⦋0⦌) v.val)
        (verdierSpanLeftContraction B).h₁
      change (verdierSpanLeftContraction B).h.app (Opposite.op ⦋0⦌)
        (v.val, stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _ at he
      rw [he]
      obtain ⟨P, hP⟩ := (functorVertexEquiv (horn 2 0 : SSet.{u}) B.obj).surjective v.val
      change functorVertex P = v.val at hP
      rw [← hP]
      change spanLeftEdge (functorVertex ((SSet.const
        (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) ≫ P)) ∈ _
      rw [SSet.const_comp]
      change PinchedHom.constant (P.app (Opposite.op ⦋0⦌)
        (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) 1 ∈ _
      exact (mem_weakEquivalences_iff_invertible h (edgeOfSimplex _)).mpr
        (invertedEdges_constant q.hom _))

private lemma verdierMarkedLeftContraction_inclusion {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q) :
    verdierMarkedLeftContraction h ≫ markedSpanInclusion B.obj (weakEquivalences i) =
      verdierMarkedLeftContractionRaw i := fullSubcomplexLift_ι _ _ _

private lemma verdierMarkedLeftContraction_source {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q) :
    verdierMarkedLeftContraction h ≫ markedSpanSource B.obj (weakEquivalences i) =
    fst (markedSpans B.obj (weakEquivalences i)) Δ[1] ≫
      markedSpanSource B.obj (weakEquivalences i) := by
  change (verdierMarkedLeftContraction h ≫ markedSpanInclusion B.obj (weakEquivalences i)) ≫
    evaluateFunctorAt (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
  rw [verdierMarkedLeftContraction_inclusion]
  dsimp only [verdierMarkedLeftContractionRaw]
  rw [Category.assoc, verdierSpanLeftContraction_source]
  rfl

private lemma verdierMarkedContractions_common_zero {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q) :
    (SSet.ι₀ : markedSpans B.obj (weakEquivalences i) ⟶ _) ≫
      verdierMarkedLeftContraction h = SSet.ι₀ ≫ verdierMarkedRightExpansion i := by
  have : Mono (markedSpanInclusion B.obj (weakEquivalences i)) := by
    dsimp only [markedSpanInclusion]
    infer_instance
  apply (cancel_mono (markedSpanInclusion B.obj (weakEquivalences i))).mp
  simp only [Category.assoc, verdierMarkedLeftContraction_inclusion,
    verdierMarkedRightExpansion_inclusion]
  dsimp only [verdierMarkedLeftContractionRaw, verdierMarkedRightExpansionRaw]
  have he : (SSet.ι₀ : markedSpans B.obj (weakEquivalences i) ⟶ _) ≫
      (markedSpanInclusion B.obj (weakEquivalences i) ▷ (Δ[1] : SSet.{u})) =
      markedSpanInclusion B.obj (weakEquivalences i) ≫ SSet.ι₀ := rfl
  rw [← Category.assoc, he, Category.assoc, (verdierSpanLeftContraction B).h₀,
    ← Category.assoc, he, Category.assoc, (verdierSpanRightExpansion B).h₀]

private def verdierFixedSourceLeftContraction {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    markedSpanFamily B.obj (weakEquivalences i) x ⊗ (Δ[1] : SSet.{u}) ⟶
      markedSpanFamily B.obj (weakEquivalences i) x :=
  vertexFiberLift (markedSpanSource B.obj (weakEquivalences i)) x
    ((vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ▷ (Δ[1] : SSet.{u})) ≫
      verdierMarkedLeftContraction h) (by
      rw [Category.assoc, verdierMarkedLeftContraction_source]
      have he : (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ▷
          (Δ[1] : SSet.{u})) ≫ fst (markedSpans B.obj (weakEquivalences i)) Δ[1] =
        fst (markedSpanFamily B.obj (weakEquivalences i) x) Δ[1] ≫
          vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x := rfl
      rw [← Category.assoc, he, Category.assoc, vertexFiberι_comp, SSet.comp_const])

private lemma verdierFixedSourceLeftContraction_inclusion {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    verdierFixedSourceLeftContraction h x ≫
      vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x =
    (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ▷ (Δ[1] : SSet.{u})) ≫
      verdierMarkedLeftContraction h := vertexFiberLift_ι _ _ _ _

private lemma verdierFixedSourceContractions_common_zero {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    (SSet.ι₀ : markedSpanFamily B.obj (weakEquivalences i) x ⟶ _) ≫
      verdierFixedSourceLeftContraction h x =
    SSet.ι₀ ≫ verdierFixedSourceRightExpansion i x := by
  apply vertexFiber_hom_ext (markedSpanSource B.obj (weakEquivalences i)) x
  simp only [Category.assoc, verdierFixedSourceLeftContraction_inclusion,
    verdierFixedSourceRightExpansion_inclusion]
  have he : (SSet.ι₀ : markedSpanFamily B.obj (weakEquivalences i) x ⟶ _) ≫
      (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ▷ (Δ[1] : SSet.{u})) =
      vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫ SSet.ι₀ := rfl
  simp only [← Category.assoc]
  rw [he]
  simp only [Category.assoc]
  rw [verdierMarkedContractions_common_zero h]

private lemma verdierSpanConstantAction (B : StableCategory.{u}) :
    (pre (SSet.const (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
        (horn 2 0 : SSet.{u}) ⟶ _)).app B.obj =
    evaluateFunctorAt (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      constantFunctorMap (horn 2 0 : SSet.{u}) B.obj := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  let v := horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  change F.app d (α ≫ 𝟙 d)
      ((horn 2 0 : SSet.{u}).map (𝟙 d) (PinchedHom.constant v d.unop.len)) =
    B.obj.map α (F.app (Opposite.op ⦋n⦌) (𝟙 _) (PinchedHom.constant v n))
  rw [Category.comp_id, CategoryTheory.Functor.map_id_apply]
  have hh := ConcreteCategory.congr_hom (F.naturality α (𝟙 _))
    (PinchedHom.constant v n)
  change F.app d ((𝟙 (Opposite.op ⦋n⦌)) ≫ α)
      ((horn 2 0 : SSet.{u}).map α (PinchedHom.constant v n)) =
    B.obj.map α (F.app (Opposite.op ⦋n⦌) (𝟙 _) (PinchedHom.constant v n)) at hh
  have hc : (horn 2 0 : SSet.{u}).map α (PinchedHom.constant v n) =
      PinchedHom.constant v d.unop.len := PinchedHom.constant_pullback v α.unop
  rw [Category.id_comp, hc] at hh
  exact hh

private lemma verdierMarkedLeftContraction_one_raw {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q) :
    (SSet.ι₁ : markedSpans B.obj (weakEquivalences i) ⟶ _) ≫
      verdierMarkedLeftContraction h ≫ markedSpanInclusion B.obj (weakEquivalences i) =
    markedSpanSource B.obj (weakEquivalences i) ≫
      constantFunctorMap (horn 2 0 : SSet.{u}) B.obj := by
  rw [verdierMarkedLeftContraction_inclusion]
  dsimp only [verdierMarkedLeftContractionRaw]
  have he : (SSet.ι₁ : markedSpans B.obj (weakEquivalences i) ⟶ _) ≫
      (markedSpanInclusion B.obj (weakEquivalences i) ▷ (Δ[1] : SSet.{u})) =
      markedSpanInclusion B.obj (weakEquivalences i) ≫ SSet.ι₁ := rfl
  rw [← Category.assoc, he, Category.assoc, (verdierSpanLeftContraction B).h₁,
    verdierSpanConstantAction]
  rfl

private def verdierIdentitySpanFamily {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) : (markedSpanFamily B.obj (weakEquivalences i) x) _⦋0⦌ :=
  identityMarkedSpanFamily (weakEquivalences i) x
    ((mem_weakEquivalences_iff_invertible h (edgeOfSimplex _)).mpr
      (invertedEdges_constant q.hom x))

private lemma verdierFixedSourceLeftContraction_one {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    (SSet.ι₁ : markedSpanFamily B.obj (weakEquivalences i) x ⟶ _) ≫
      verdierFixedSourceLeftContraction h x = SSet.const (verdierIdentitySpanFamily h x) := by
  apply vertexFiber_hom_ext (markedSpanSource B.obj (weakEquivalences i)) x
  have : Mono (markedSpanInclusion B.obj (weakEquivalences i)) := by
    dsimp only [markedSpanInclusion]
    infer_instance
  apply (cancel_mono (markedSpanInclusion B.obj (weakEquivalences i))).mp
  simp only [Category.assoc, verdierFixedSourceLeftContraction_inclusion,
    SSet.const_comp]
  have he : (SSet.ι₁ : markedSpanFamily B.obj (weakEquivalences i) x ⟶ _) ≫
      (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ▷ (Δ[1] : SSet.{u})) =
      vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫ SSet.ι₁ := rfl
  rw [← Category.assoc, ← Category.assoc, he]
  simp only [Category.assoc]
  rw [verdierMarkedLeftContraction_one_raw, ← Category.assoc, vertexFiberι_comp,
    SSet.const_comp, constantFunctorMap_vertex]
  rfl

private def verdierFixedSourceDenominator {A B : StableCategory.{u}}
    (i : ExactMap A B) (x : B.obj _⦋0⦌) :
    markedSpanFamily B.obj (weakEquivalences i) x ⟶
      markedSpanFamily B.obj (weakEquivalences i) x :=
  SSet.ι₀ ≫ verdierFixedSourceRightExpansion i x

private def verdierFixedSourceRightHomotopy {A B : StableCategory.{u}}
    (i : ExactMap A B) (x : B.obj _⦋0⦌) :
    SSet.Homotopy (verdierFixedSourceDenominator i x) (𝟙 _) where
  h := verdierFixedSourceRightExpansion i x
  h₀ := rfl
  h₁ := verdierFixedSourceRightExpansion_one i x
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

private def verdierFixedSourceLeftHomotopy {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    SSet.Homotopy (verdierFixedSourceDenominator i x)
      (SSet.const (verdierIdentitySpanFamily h x)) where
  h := verdierFixedSourceLeftContraction h x
  h₀ := verdierFixedSourceContractions_common_zero h x
  h₁ := verdierFixedSourceLeftContraction_one h x
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

private lemma denominatorSpanLeftContraction_target :
    (denominatorSpanLeftContraction : (Δ[1] : SSet.{u}) ⟶ _) ≫
      evaluateFunctorAt (horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = horn₂₀.ι₀₁ := by
  change denominatorSpanLeftContraction ≫
    (pre horn₂₀.ι₀₂).app (horn 2 0 : SSet.{u}) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  rw [← Category.assoc, denominatorSpanLeftContraction, stable_spanFamilyOfArrows_right,
    curry_evaluateFunctorAt_interval]
  rfl

private lemma verdierSpanLeftContraction_target (B : StableCategory.{u}) :
    (verdierSpanLeftContraction B).h ≫
      evaluateFunctorAt (horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
    (β_ ((ihom (horn 2 0 : SSet.{u})).obj B.obj) (Δ[1] : SSet.{u})).hom ≫
      uncurry ((pre horn₂₀.ι₀₁).app B.obj) := by
  let F := denominatorSpanLeftContraction ≫
    functorPrecompositionMap (horn 2 0 : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv F)) ≫ _ = _
  rw [Equiv.symm_apply_apply, ← uncurry_natural_right]
  have he : F ≫ (ihom ((ihom (horn 2 0 : SSet.{u})).obj B.obj)).map
      (evaluateFunctorAt (horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      horn₂₀.ι₀₁ ≫ verdierSpanSourceEvaluation B := by
    dsimp only [F]
    rw [Category.assoc, verdierSpanSourceRestriction_natural, ← Category.assoc,
      denominatorSpanLeftContraction_target]
  rw [he]
  have hf := internalHomFlipHomEquiv_pre_app horn₂₀.ι₀₁
    (𝟙 ((ihom (horn 2 0 : SSet.{u})).obj B.obj))
  rw [Category.id_comp] at hf
  change internalHomFlipHomEquiv _ _ _ ((pre horn₂₀.ι₀₁).app B.obj) =
    horn₂₀.ι₀₁ ≫ verdierSpanSourceEvaluation B at hf
  rw [← hf]
  change uncurry (curry ((β_ _ _).hom ≫ uncurry ((pre horn₂₀.ι₀₁).app B.obj))) = _
  rw [uncurry_curry]

private lemma verdierFixedSourceLeftHomotopy_projection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    (verdierFixedSourceLeftHomotopy h x).h ≫
      markedSpanFamilyProjection B.obj (weakEquivalences i) x =
    (β_ (markedSpanFamily B.obj (weakEquivalences i) x) (Δ[1] : SSet.{u})).hom ≫
      uncurry (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
        markedSpanInclusion B.obj (weakEquivalences i) ≫ (pre horn₂₀.ι₀₁).app B.obj) := by
  change (verdierFixedSourceLeftContraction h x ≫
    vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x) ≫
      markedSpanInclusion B.obj (weakEquivalences i) ≫
        evaluateFunctorAt (horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
  rw [verdierFixedSourceLeftContraction_inclusion, Category.assoc,
    ← Category.assoc (verdierMarkedLeftContraction h),
    verdierMarkedLeftContraction_inclusion]
  dsimp only [verdierMarkedLeftContractionRaw]
  simp only [Category.assoc]
  rw [verdierSpanLeftContraction_target]
  simp only [uncurry_natural_left]
  rfl

private lemma verdierFixedSourceLeftHomotopy_denominator {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) (v : (markedSpanFamily B.obj (weakEquivalences i) x) _⦋0⦌) :
    (markedSpanFamilyProjection B.obj (weakEquivalences i) x).app (Opposite.op ⦋1⦌)
      (simplicialHomotopyVertexEdge (verdierFixedSourceLeftHomotopy h x) v).edge =
        spanLeftEdge v.val.val := by
  have he := congrArg (fun F => F.app (Opposite.op ⦋1⦌)
    (PinchedHom.constant v 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))))
      (verdierFixedSourceLeftHomotopy_projection h x)
  change (markedSpanFamilyProjection B.obj (weakEquivalences i) x).app (Opposite.op ⦋1⦌)
    ((verdierFixedSourceLeftHomotopy h x).h.app (Opposite.op ⦋1⦌)
      (PinchedHom.constant v 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))) =
    (uncurry (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
      markedSpanInclusion B.obj (weakEquivalences i) ≫
        (pre horn₂₀.ι₀₁).app B.obj)).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1) at he
  have ht := intervalFunctorVertexEdge_curry
    (uncurry (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
      markedSpanInclusion B.obj (weakEquivalences i) ≫ (pre horn₂₀.ι₀₁).app B.obj)) v
  rw [curry_uncurry] at ht
  change (markedSpanFamilyProjection B.obj (weakEquivalences i) x).app (Opposite.op ⦋1⦌)
    ((verdierFixedSourceLeftHomotopy h x).h.app (Opposite.op ⦋1⦌)
      ((Truncated.Edge.id (X := (truncation 2).obj
        (markedSpanFamily B.obj (weakEquivalences i) x)) v).edge,
          homotopyIntervalEdge.edge)) = _
  have hi : (homotopyIntervalEdge : Truncated.Edge
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).edge =
      SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [← pinchedConstant_one, hi]
  exact he.trans ht.symm

private lemma verdierFixedSourceLeftHomotopy_quotient_invertible
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)
    (v : (markedSpanFamily B.obj (weakEquivalences i) x) _⦋0⦌) :
    IsInvertibleEdge
      ((((simplicialHomotopyVertexEdge (verdierFixedSourceLeftHomotopy h x) v).map
        (markedSpanFamilyProjection B.obj (weakEquivalences i) x)).toTruncated).map
          ((truncation 2).map q.hom)) := by
  apply (mem_weakEquivalences_iff_invertible h _).mp
  change (markedSpanFamilyProjection B.obj (weakEquivalences i) x).app (Opposite.op ⦋1⦌)
    (simplicialHomotopyVertexEdge (verdierFixedSourceLeftHomotopy h x) v).edge ∈ _
  rw [verdierFixedSourceLeftHomotopy_denominator]
  exact fullSubcomplexOnVertices_vertex v.val

private lemma verdierIdentitySpanFamily_projection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    (markedSpanFamilyProjection B.obj (weakEquivalences i) x).app
      (Opposite.op ⦋0⦌) (verdierIdentitySpanFamily h x) = x :=
  identityMarkedSpanFamily_projection _ _ _

private def verdierFixedSourceLeftQuotientHomotopy {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    SSet.Homotopy (verdierFixedSourceDenominator i x ≫
      markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
        (SSet.const (q.hom.app (Opposite.op ⦋0⦌) x)) := by
  let H := functorHomotopyPostcomp (verdierFixedSourceLeftHomotopy h x)
    (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
  refine { h := H.h, h₀ := H.h₀, h₁ := ?_, rel := H.rel }
  change SSet.ι₁ ≫ H.h = SSet.const (q.hom.app (Opposite.op ⦋0⦌) x)
  rw [H.h₁, SSet.const_comp]
  change SSet.const (q.hom.app (Opposite.op ⦋0⦌)
    ((markedSpanFamilyProjection B.obj (weakEquivalences i) x).app
      (Opposite.op ⦋0⦌) (verdierIdentitySpanFamily h x))) = _
  rw [verdierIdentitySpanFamily_projection]

/-- 選択済みの同じ実変形の底像を可逆化する。単なる頂点ごとの同型の選択ではない。 -/
private def verdierFixedSourceDenominatorImageIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    FunctorIso (verdierFixedSourceDenominator i x ≫
      markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
        (SSet.const (q.hom.app (Opposite.op ⦋0⦌) x)) := by
  apply functorIsoOfPointwiseInvertibleHomotopy (verdierFixedSourceLeftQuotientHomotopy h x)
  intro v
  exact (isInvertibleEdge_congr
    (e := (simplicialHomotopyVertexEdge (verdierFixedSourceLeftQuotientHomotopy h x) v).toTruncated)
    (f := (((simplicialHomotopyVertexEdge (verdierFixedSourceLeftHomotopy h x) v).map
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x)).toTruncated).map
        ((truncation 2).map q.hom))
    rfl).mpr
    (verdierFixedSourceLeftHomotopy_quotient_invertible h x v)

/-- 元の族を分類先へ送る実写像が与えられたとき、同じ分母変形をそこで可逆化する。
実写像自体の供給をこの私有補題の仮定から取り除いたとは主張しない。 -/
private def verdierLiftedDenominatorIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    FunctorIso (verdierFixedSourceDenominator i x ≫ U)
      (SSet.const (verdierIdentitySpanFamily h x) ≫ U) := by
  let H := functorHomotopyPostcomp (verdierFixedSourceLeftHomotopy h x) U
  apply functorIsoOfPointwiseInvertibleHomotopy H
  intro v
  apply leftFibration_reflects_invertibleEdge p
    (simplicialHomotopyVertexEdge H v).toTruncated
  have he := congrArg (fun F => F.app (Opposite.op ⦋1⦌)
    (simplicialHomotopyVertexEdge (verdierFixedSourceLeftHomotopy h x) v).edge) hU
  change p.app (Opposite.op ⦋1⦌) (U.app (Opposite.op ⦋1⦌)
    (simplicialHomotopyVertexEdge (verdierFixedSourceLeftHomotopy h x) v).edge) =
    q.hom.app (Opposite.op ⦋1⦌)
      ((markedSpanFamilyProjection B.obj (weakEquivalences i) x).app (Opposite.op ⦋1⦌)
        (simplicialHomotopyVertexEdge (verdierFixedSourceLeftHomotopy h x) v).edge) at he
  exact (isInvertibleEdge_congr
    (e := (simplicialHomotopyVertexEdge H v).toTruncated.map ((truncation 2).map p))
    (f := (((simplicialHomotopyVertexEdge (verdierFixedSourceLeftHomotopy h x) v).map
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x)).toTruncated).map
        ((truncation 2).map q.hom)) he).mpr
      (verdierFixedSourceLeftHomotopy_quotient_invertible h x v)

private def verdierLiftedRightHomotopy {A B : StableCategory.{u}}
    (i : ExactMap A B) (x : B.obj _⦋0⦌) {E : SSet.{u}}
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E) :
    SSet.Homotopy (verdierFixedSourceDenominator i x ≫ U) U := by
  let J := functorHomotopyPostcomp (verdierFixedSourceRightHomotopy i x) U
  refine { h := J.h, h₀ := J.h₀, h₁ := ?_, rel := J.rel }
  change SSet.ι₁ ≫ J.h = U
  rw [J.h₁, Category.id_comp]

private def verdierLiftedIdentityCone {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    FunctorHom (SSet.const (verdierIdentitySpanFamily h x) ≫ U) U :=
  (verdierLiftedDenominatorIso h x p U hU).inv ≫
    Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (verdierLiftedRightHomotopy i x U))

private lemma denominatorSpanRightExpansion_target :
    (denominatorSpanRightExpansion : (Δ[1] : SSet.{u}) ⟶ _) ≫
      evaluateFunctorAt (horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = horn₂₀.ι₀₂ := by
  change denominatorSpanRightExpansion ≫
    (pre horn₂₀.ι₀₂).app (horn 2 0 : SSet.{u}) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  rw [← Category.assoc, denominatorSpanRightExpansion, stable_spanFamilyOfArrows_right,
    curry_evaluateFunctorAt_interval, ← Category.assoc,
    intervalMinimum_first_one, Category.id_comp]

private lemma verdierSpanRightExpansion_target (B : StableCategory.{u}) :
    (verdierSpanRightExpansion B).h ≫
      evaluateFunctorAt (horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
    (β_ ((ihom (horn 2 0 : SSet.{u})).obj B.obj) (Δ[1] : SSet.{u})).hom ≫
      uncurry ((pre horn₂₀.ι₀₂).app B.obj) := by
  let F := denominatorSpanRightExpansion ≫
    functorPrecompositionMap (horn 2 0 : SSet.{u}) (horn 2 0 : SSet.{u}) B.obj
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv F)) ≫ _ = _
  rw [Equiv.symm_apply_apply, ← uncurry_natural_right]
  have he : F ≫ (ihom ((ihom (horn 2 0 : SSet.{u})).obj B.obj)).map
      (evaluateFunctorAt (horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      horn₂₀.ι₀₂ ≫ verdierSpanSourceEvaluation B := by
    dsimp only [F]
    rw [Category.assoc, verdierSpanSourceRestriction_natural, ← Category.assoc,
      denominatorSpanRightExpansion_target]
  rw [he]
  have hf := internalHomFlipHomEquiv_pre_app horn₂₀.ι₀₂
    (𝟙 ((ihom (horn 2 0 : SSet.{u})).obj B.obj))
  rw [Category.id_comp] at hf
  change internalHomFlipHomEquiv _ _ _ ((pre horn₂₀.ι₀₂).app B.obj) =
    horn₂₀.ι₀₂ ≫ verdierSpanSourceEvaluation B at hf
  rw [← hf]
  change uncurry (curry ((β_ _ _).hom ≫ uncurry ((pre horn₂₀.ι₀₂).app B.obj))) = _
  rw [uncurry_curry]

private lemma verdierFixedSourceRightHomotopy_projection {A B : StableCategory.{u}}
    (i : ExactMap A B) (x : B.obj _⦋0⦌) :
    (verdierFixedSourceRightHomotopy i x).h ≫
      markedSpanFamilyProjection B.obj (weakEquivalences i) x =
    (β_ (markedSpanFamily B.obj (weakEquivalences i) x) (Δ[1] : SSet.{u})).hom ≫
      uncurry (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
        markedSpanInclusion B.obj (weakEquivalences i) ≫ (pre horn₂₀.ι₀₂).app B.obj) := by
  change (verdierFixedSourceRightExpansion i x ≫
    vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x) ≫
      markedSpanInclusion B.obj (weakEquivalences i) ≫
        evaluateFunctorAt (horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
  rw [verdierFixedSourceRightExpansion_inclusion, Category.assoc,
    ← Category.assoc (verdierMarkedRightExpansion i),
    verdierMarkedRightExpansion_inclusion]
  dsimp only [verdierMarkedRightExpansionRaw]
  simp only [Category.assoc]
  rw [verdierSpanRightExpansion_target]
  simp only [uncurry_natural_left]
  rfl

private def verdierFixedSourceRightQuotientHomotopy {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    SSet.Homotopy (verdierFixedSourceDenominator i x ≫
      markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
        (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) := by
  let H := functorHomotopyPostcomp (verdierFixedSourceRightHomotopy i x)
    (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
  refine { h := H.h, h₀ := H.h₀, h₁ := ?_, rel := H.rel }
  change SSet.ι₁ ≫ H.h = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom
  rw [H.h₁, Category.id_comp]

private def verdierSpanQuotientEvaluationFamily {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    markedSpanFamily B.obj (weakEquivalences i) x ⟶ (ihom (Δ[1] : SSet.{u})).obj C.obj :=
  vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
    fractionSpanEvaluation q.hom (weakEquivalences i) h.inverts

private def verdierSpanQuotientEvaluationHomotopy {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    SSet.Homotopy (SSet.const (q.hom.app (Opposite.op ⦋0⦌) x))
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) where
  h := (β_ (markedSpanFamily B.obj (weakEquivalences i) x) (Δ[1] : SSet.{u})).hom ≫
    uncurry (verdierSpanQuotientEvaluationFamily h x)
  h₀ := by
    change prismEndpoint 0 (markedSpanFamily B.obj (weakEquivalences i) x) ≫
      uncurry (verdierSpanQuotientEvaluationFamily h x) =
        SSet.const (q.hom.app (Opposite.op ⦋0⦌) x)
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    dsimp only [verdierSpanQuotientEvaluationFamily]
    rw [Category.assoc, fractionSpanEvaluation_source]
    change (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
      markedSpanSource B.obj (weakEquivalences i)) ≫ q.hom = _
    rw [vertexFiberι_comp, SSet.const_comp]
  h₁ := by
    change prismEndpoint 1 (markedSpanFamily B.obj (weakEquivalences i) x) ≫
      uncurry (verdierSpanQuotientEvaluationFamily h x) =
        markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    dsimp only [verdierSpanQuotientEvaluationFamily]
    rw [Category.assoc, fractionSpanEvaluation_target]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

private def verdierSpanQuotientTriangleFamily {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    markedSpanFamily B.obj (weakEquivalences i) x ⟶ (ihom (Δ[2] : SSet.{u})).obj C.obj :=
  vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
    fractionEvaluationTriangle q.hom (weakEquivalences i) h.inverts

private lemma verdierSpanQuotientTriangle_leg {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) (k : (Δ[1] : SSet.{u}) ⟶ horn 2 0) (j : Fin 3)
    (hk : k ≫ (horn 2 0).ι = stdSimplex.δ j) :
    verdierSpanQuotientTriangleFamily h x ≫ (pre (stdSimplex.δ j)).app C.obj =
    vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
      markedSpanInclusion B.obj (weakEquivalences i) ≫ (pre k).app B.obj ≫
        (ihom (Δ[1] : SSet.{u})).map q.hom := by
  have hp : (pre (stdSimplex.δ j)).app C.obj =
      (pre (horn 2 0).ι).app C.obj ≫ (pre k).app C.obj := by
    rw [← NatTrans.comp_app, ← pre_map, hk]
  dsimp only [verdierSpanQuotientTriangleFamily]
  rw [hp, ← Category.assoc,
    Category.assoc (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x),
    fractionEvaluationTriangle_span]
  simp only [Category.assoc]
  rw [(pre k).naturality q.hom]

private lemma verdierLeftQuotientHomotopy_leg {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    (verdierFixedSourceLeftQuotientHomotopy h x).h =
    (β_ (markedSpanFamily B.obj (weakEquivalences i) x) (Δ[1] : SSet.{u})).hom ≫
      uncurry (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
        markedSpanInclusion B.obj (weakEquivalences i) ≫ (pre horn₂₀.ι₀₁).app B.obj ≫
          (ihom (Δ[1] : SSet.{u})).map q.hom) := by
  change (verdierFixedSourceLeftHomotopy h x).h ≫
    markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom = _
  rw [← Category.assoc, verdierFixedSourceLeftHomotopy_projection, Category.assoc,
    ← uncurry_natural_right]
  rfl

private lemma verdierRightQuotientHomotopy_leg {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    (verdierFixedSourceRightQuotientHomotopy h x).h =
    (β_ (markedSpanFamily B.obj (weakEquivalences i) x) (Δ[1] : SSet.{u})).hom ≫
      uncurry (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
        markedSpanInclusion B.obj (weakEquivalences i) ≫ (pre horn₂₀.ι₀₂).app B.obj ≫
          (ihom (Δ[1] : SSet.{u})).map q.hom) := by
  change (verdierFixedSourceRightHomotopy i x).h ≫
    markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom = _
  rw [← Category.assoc, verdierFixedSourceRightHomotopy_projection, Category.assoc,
    ← uncurry_natural_right]
  rfl

/-- 全 roof 族の二変形と元の選択済み分数評価は、同じ実関手三角形の三辺。 -/
private def verdierSpanQuotientCompositionTriangle {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    FunctorCompositionTriangle (verdierFixedSourceLeftQuotientHomotopy h x)
      (verdierSpanQuotientEvaluationHomotopy h x)
        (verdierFixedSourceRightQuotientHomotopy h x) where
  diagram := internalHomFlipHomEquiv _ _ _ (verdierSpanQuotientTriangleFamily h x)
  face_zero := by
    rw [← internalHomFlipHomEquiv_pre_app]
    rfl
  face_one := by
    rw [← internalHomFlipHomEquiv_pre_app,
      verdierSpanQuotientTriangle_leg h x horn₂₀.ι₀₂ (1 : Fin 3) rfl,
      verdierRightQuotientHomotopy_leg]
    rfl
  face_two := by
    rw [← internalHomFlipHomEquiv_pre_app,
      verdierSpanQuotientTriangle_leg h x horn₂₀.ι₀₁ (2 : Fin 3) rfl,
      verdierLeftQuotientHomotopy_leg]
    rfl

private lemma verdierSpanQuotientEvaluation_hom {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    (verdierFixedSourceDenominatorImageIso h x).inv ≫
      Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (verdierFixedSourceRightQuotientHomotopy h x)) =
    Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (verdierSpanQuotientEvaluationHomotopy h x)) := by
  apply (Iso.inv_comp_eq (verdierFixedSourceDenominatorImageIso h x)).mpr
  exact (verdierSpanQuotientCompositionTriangle h x).hom_eq.symm

private def verdierLiftedIdentityHomotopy {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    SSet.Homotopy
      (SSet.const (U.app (Opposite.op ⦋0⦌) (verdierIdentitySpanFamily h x))) U := by
  let H := functorHomHomotopy (verdierLiftedIdentityCone h x p U hU)
  refine { h := H.h, h₀ := ?_, h₁ := H.h₁, rel := H.rel }
  change SSet.ι₀ ≫ H.h =
    SSet.const (U.app (Opposite.op ⦋0⦌) (verdierIdentitySpanFamily h x))
  rw [H.h₀, SSet.const_comp]

private def verdierLiftedIdentityConeRealization {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    HomotopyConeRealization (verdierLiftedIdentityHomotopy h x p U hU) :=
  homotopyConeRealization _

private def verdierLiftedIdentityCoslice {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    markedSpanFamily B.obj (weakEquivalences i) x ⟶
      sliceUnder (SSet.yonedaEquiv.symm
        (U.app (Opposite.op ⦋0⦌) (verdierIdentitySpanFamily h x))) :=
  sliceUnderCurry (verdierLiftedIdentityConeRealization h x p U hU).cone.val (by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    change (verdierLiftedIdentityConeRealization h x p U hU).cone.vertex = _
    exact (verdierLiftedIdentityConeRealization h x p U hU).vertex_eq)

private lemma verdierLiftedIdentityCoslice_projection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    verdierLiftedIdentityCoslice h x p U hU ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm
        (U.app (Opposite.op ⦋0⦌) (verdierIdentitySpanFamily h x))) = U := by
  rw [verdierLiftedIdentityCoslice, sliceUnderCurry_projection]
  exact (verdierLiftedIdentityConeRealization h x p U hU).cone.property

private lemma verdierLiftedIdentityCone_triangle {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    Nonempty (Truncated.Edge.CompStruct
      (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (verdierFixedSourceLeftHomotopy h x) U))
      (functorEdgeOfSimplicialHomotopy
        (functorHomHomotopy (verdierLiftedIdentityCone h x p U hU)))
      (functorEdgeOfSimplicialHomotopy
        (verdierLiftedRightHomotopy i x U))) := by
  apply compStruct_nonempty_of_homMk_fac
  rw [functorHomHomotopy_hom]
  change (verdierLiftedDenominatorIso h x p U hU).hom ≫
    ((verdierLiftedDenominatorIso h x p U hU).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

private def verdierLiftedIdentityConeImageHomotopy {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    SSet.Homotopy (SSet.const (q.hom.app (Opposite.op ⦋0⦌) x))
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) := by
  let H := functorHomHomotopy (verdierLiftedIdentityCone h x p U hU)
  let J := functorHomotopyPostcomp H p
  refine { h := J.h, h₀ := ?_, h₁ := ?_, rel := J.rel }
  · change SSet.ι₀ ≫ J.h = SSet.const (q.hom.app (Opposite.op ⦋0⦌) x)
    rw [J.h₀, Category.assoc, hU, SSet.const_comp]
    change SSet.const (q.hom.app (Opposite.op ⦋0⦌)
      ((markedSpanFamilyProjection B.obj (weakEquivalences i) x).app
        (Opposite.op ⦋0⦌) (verdierIdentitySpanFamily h x))) = _
    rw [verdierIdentitySpanFamily_projection]
  · change SSet.ι₁ ≫ J.h = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom
    rw [J.h₁, hU]

private lemma verdierLiftedIdentityConeImage_triangle {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    Nonempty (Truncated.Edge.CompStruct
      (functorEdgeOfSimplicialHomotopy (verdierFixedSourceLeftQuotientHomotopy h x))
      (functorEdgeOfSimplicialHomotopy (verdierLiftedIdentityConeImageHomotopy h x p U hU))
      (functorEdgeOfSimplicialHomotopy (verdierFixedSourceRightQuotientHomotopy h x))) := by
  obtain ⟨τ⟩ := verdierLiftedIdentityCone_triangle h x p U hU
  let P := (ihom (markedSpanFamily B.obj (weakEquivalences i) x)).map p
  let τ' := τ.map ((truncation 2).map P)
  have hl : (((functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (verdierFixedSourceLeftHomotopy h x) U)).map
        ((truncation 2).map P))).edge =
      (functorEdgeOfSimplicialHomotopy (verdierFixedSourceLeftQuotientHomotopy h x)).edge := by
    change P.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
      (curry ((verdierFixedSourceLeftHomotopy h x).h ≫ U))) =
      SSet.yonedaEquiv (curry ((verdierFixedSourceLeftHomotopy h x).h ≫
        markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom))
    rw [← SSet.yonedaEquiv_comp]
    dsimp only [P]
    rw [← curry_natural_right, Category.assoc, hU]
  have hr : (((functorEdgeOfSimplicialHomotopy
      (verdierLiftedRightHomotopy i x U)).map ((truncation 2).map P))).edge =
      (functorEdgeOfSimplicialHomotopy (verdierFixedSourceRightQuotientHomotopy h x)).edge := by
    change P.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
      (curry ((verdierFixedSourceRightHomotopy i x).h ≫ U))) =
      SSet.yonedaEquiv (curry ((verdierFixedSourceRightHomotopy i x).h ≫
        markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom))
    rw [← SSet.yonedaEquiv_comp]
    dsimp only [P]
    rw [← curry_natural_right, Category.assoc, hU]
  have hc : (((functorEdgeOfSimplicialHomotopy
      (functorHomHomotopy (verdierLiftedIdentityCone h x p U hU))).map
        ((truncation 2).map P))).edge =
      (functorEdgeOfSimplicialHomotopy
        (verdierLiftedIdentityConeImageHomotopy h x p U hU)).edge := by
    change P.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
      (curry (functorHomHomotopy (verdierLiftedIdentityCone h x p U hU)).h)) =
      SSet.yonedaEquiv (curry ((functorHomHomotopy
        (verdierLiftedIdentityCone h x p U hU)).h ≫ p))
    rw [← SSet.yonedaEquiv_comp]
    dsimp only [P]
    rw [← curry_natural_right]
  exact ⟨⟨τ'.simplex, τ'.d₂.trans hl, τ'.d₀.trans hc, τ'.d₁.trans hr⟩⟩

private lemma verdierLiftedIdentityConeImage_evaluation {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (verdierLiftedIdentityConeImageHomotopy h x p U hU)) =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (verdierSpanQuotientEvaluationHomotopy h x)) := by
  obtain ⟨τ⟩ := verdierLiftedIdentityConeImage_triangle h x p U hU
  apply (cancel_epi (verdierFixedSourceDenominatorImageIso h x).hom).mp
  exact (Truncated.HomotopyCategory.homMk_comp_homMk τ).trans
    (verdierSpanQuotientCompositionTriangle h x).hom_eq.symm

private def verdierFixedRoofImageHomotopy {A B C : StableCategory.{u}}
    (i : ExactMap A B) (q : ExactMap B C) (x y : B.obj _⦋0⦌)
    (H : SSet.Homotopy (SSet.const (q.hom.app _ x))
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)) :
    SSet.Homotopy
      (SSet.const (X := fixedMarkedSpans B.obj (weakEquivalences i) x y) (q.hom.app _ x))
      (SSet.const (q.hom.app _ y)) := by
  let J := functorHomotopyPrecomp H (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y)
  exact {
    h := J.h
    h₀ := by
      change SSet.ι₀ ≫ J.h = SSet.const (q.hom.app _ x)
      simpa only [SSet.comp_const] using J.h₀
    h₁ := by
      change SSet.ι₁ ≫ J.h = SSet.const (q.hom.app _ y)
      exact J.h₁.trans (fixedMarkedSpanToFamily_target q.hom (weakEquivalences i) x y)
    rel := J.rel }

private lemma verdierFixedRoofImageHomotopy_homEq {A B C : StableCategory.{u}}
    (i : ExactMap A B) (q : ExactMap B C) (x y : B.obj _⦋0⦌)
    (H H' : SSet.Homotopy (SSet.const (q.hom.app _ x))
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom))
    (he : Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H')) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (verdierFixedRoofImageHomotopy i q x y H)) =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (verdierFixedRoofImageHomotopy i q x y H')) := by
  let L := functorHomotopyRefl
    (SSet.const (X := markedSpanFamily B.obj (weakEquivalences i) x) (q.hom.app _ x))
  obtain ⟨T⟩ := nonempty_functorCompositionTriangle_of_homEq L H H' (by
    rw [functorHomotopyRefl_hom]
    exact (Category.id_comp _).trans he)
  let L' := functorHomotopyRefl
    (SSet.const (X := fixedMarkedSpans B.obj (weakEquivalences i) x y) (q.hom.app _ x))
  let T' := T.precompOfRaw (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y)
    L' (verdierFixedRoofImageHomotopy i q x y H)
      (verdierFixedRoofImageHomotopy i q x y H') (by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro a
        rfl) rfl rfl
  have ht := T'.hom_eq
  rw [functorHomotopyRefl_hom] at ht
  exact (Category.id_comp _).symm.trans ht

private def verdierFixedLiftedConeEvaluation {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    fixedMarkedSpans B.obj (weakEquivalences i) x y ⟶
      intervalMappingSpace (q.hom.app _ x) (q.hom.app _ y) :=
  intervalFamilyOfEdge (functorEdgeOfSimplicialHomotopy
    (verdierFixedRoofImageHomotopy i q x y
      (verdierLiftedIdentityConeImageHomotopy h x p U hU)))

private lemma verdierFixedRoofEvaluation_edge {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) :
    functorEdgeOfSimplicialHomotopy (verdierFixedRoofImageHomotopy i q x y
      (verdierSpanQuotientEvaluationHomotopy h x)) =
    intervalFamilyEdge (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y) := by
  apply Truncated.Edge.ext
  change SSet.yonedaEquiv (curry
    ((fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (markedSpanFamily B.obj (weakEquivalences i) x) Δ[1]).hom ≫
        uncurry (verdierSpanQuotientEvaluationFamily h x))) =
    SSet.yonedaEquiv (curry
      ((β_ (fixedMarkedSpans B.obj (weakEquivalences i) x y) Δ[1]).hom ≫
        intervalMappingUncurry
          (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y)))
  apply congrArg SSet.yonedaEquiv
  apply congrArg curry
  have hn : (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y ▷
      (Δ[1] : SSet.{u})) ≫
        (β_ (markedSpanFamily B.obj (weakEquivalences i) x) Δ[1]).hom =
      (β_ (fixedMarkedSpans B.obj (weakEquivalences i) x y) Δ[1]).hom ≫
        (Δ[1] ◁ fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, hn, Category.assoc, ← uncurry_natural_left]
  change (β_ (fixedMarkedSpans B.obj (weakEquivalences i) x y) Δ[1]).hom ≫
      uncurry (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y ≫
        (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x ≫
          fractionSpanEvaluation q.hom (weakEquivalences i) h.inverts)) =
    (β_ (fixedMarkedSpans B.obj (weakEquivalences i) x y) Δ[1]).hom ≫
      uncurry (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y ≫
        vertexFiberι ((pre (boundary 1).ι).app C.obj)
          (functorVertex (intervalMappingBoundary (q.hom.app _ x) (q.hom.app _ y))))
  rw [fixedFractionEvaluation_inclusion, ← Category.assoc,
    fixedMarkedSpanToFamily_inclusion]

private lemma verdierFixedLiftedConeEvaluation_hom {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    intervalFamilyHom (verdierFixedLiftedConeEvaluation h x y p U hU) =
      intervalFamilyHom
        (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y) := by
  have he := verdierFixedRoofImageHomotopy_homEq i q x y
    (verdierLiftedIdentityConeImageHomotopy h x p U hU)
    (verdierSpanQuotientEvaluationHomotopy h x)
    (verdierLiftedIdentityConeImage_evaluation h x p U hU)
  change Truncated.HomotopyCategory.homMk
      (intervalFamilyEdge (intervalFamilyOfEdge (functorEdgeOfSimplicialHomotopy
        (verdierFixedRoofImageHomotopy i q x y
          (verdierLiftedIdentityConeImageHomotopy h x p U hU))))) = _
  rw [intervalFamilyEdge_ofEdge]
  exact he.trans (congrArg Truncated.HomotopyCategory.homMk
    (verdierFixedRoofEvaluation_edge h x y))

private def verdierFixedLiftedConeEvaluationHomotopy {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    SSet.Homotopy (verdierFixedLiftedConeEvaluation h x y p U hU)
      (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y) :=
  Classical.choice (intervalFamilyHom_eq_iff_homotopy.mp
    (verdierFixedLiftedConeEvaluation_hom h x y p U hU))

private def verdierFixedLiftedConeEvaluationIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    FunctorIso (verdierFixedLiftedConeEvaluation h x y p U hU)
      (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y) := by
  let H := verdierFixedLiftedConeEvaluationHomotopy h x y p U hU
  haveI : IsIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj
      ((ihom (fixedMarkedSpans B.obj (weakEquivalences i) x y)).obj
        (intervalMappingSpace (q.hom.app _ x) (q.hom.app _ y)))) _
  exact asIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))

private lemma verdierLiftedIdentity_vertex_image {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    p.app _ (U.app _ (verdierIdentitySpanFamily h x)) = q.hom.app _ x := by
  have he := congrArg (fun F => F.app (Opposite.op ⦋0⦌)
    (verdierIdentitySpanFamily h x)) hU
  change _ = q.hom.app _
    ((markedSpanFamilyProjection B.obj (weakEquivalences i) x).app _
      (verdierIdentitySpanFamily h x)) at he
  rw [verdierIdentitySpanFamily_projection] at he
  exact he

private def verdierLiftedConeImageData {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    PointSourceCosliceData (q.hom.app _ x)
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
      (homotopyFatCone (verdierLiftedIdentityHomotopy h x p U hU) ≫ p) := by
  let H := verdierLiftedIdentityHomotopy h x p U hU
  let R := verdierLiftedIdentityConeRealization h x p U hU
  have hv : SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x)) ≫ p =
      SSet.yonedaEquiv.symm (q.hom.app _ x) := by
    rw [SSet.yonedaEquiv_symm_comp, verdierLiftedIdentity_vertex_image h x p U hU]
  have hl : joinInl Δ[0] (markedSpanFamily B.obj (weakEquivalences i) x) ≫
      R.cone.val = SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x)) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact R.vertex_eq
  have hF : fatJoinEndpointInclusion Δ[0] (markedSpanFamily B.obj (weakEquivalences i) x) ≫
      homotopyFatCone H = joinEndpointDesc
        (SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x))) U := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a =>
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (homotopyFatCone_inl H) n) a
    | inr a =>
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (homotopyFatCone_inr H) n) a
  let J := functorHomotopyPostcomp R.comparison p
  refine {
    cone := R.cone.val ≫ p
    left := by rw [← Category.assoc, hl, hv]
    right := by rw [← Category.assoc, R.cone.property, hU]
    fatLeft := by rw [← Category.assoc, homotopyFatCone_inl, hv]
    fatRight := by rw [← Category.assoc, homotopyFatCone_inr, hU]
    homotopy := {
      h := J.h
      h₀ := by
        change SSet.ι₀ ≫ J.h = _ ≫ (R.cone.val ≫ p)
        exact J.h₀.trans (Category.assoc _ _ _)
      h₁ := J.h₁
      rel := J.rel }
    fixed := ?_ }
  change (_ ▷ (Δ[1] : SSet.{u})) ≫ (R.comparison.h ≫ p) =
    _ ≫ _ ≫ (homotopyFatCone H ≫ p)
  rw [← Category.assoc, R.boundary, Category.assoc, ← hF]
  simp only [Category.assoc]

private lemma verdierLiftedConeImage_fixedPrism {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    leftIntervalFatPrism (fixedMarkedSpans B.obj (weakEquivalences i) x y) ≫
      (fatJoinMap (𝟙 (Δ[0] : SSet.{u}))
        (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y) ≫
          (homotopyFatCone (verdierLiftedIdentityHomotopy h x p U hU) ≫ p)) =
      intervalMappingUncurry (verdierFixedLiftedConeEvaluation h x y p U hU) := by
  let H := verdierLiftedIdentityHomotopy h x p U hU
  let σ := fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y
  let K := markedSpanFamily B.obj (weakEquivalences i) x
  let P := fixedMarkedSpans B.obj (weakEquivalences i) x y
  have ha : intervalFamilyHomotopy (verdierFixedLiftedConeEvaluation h x y p U hU) =
      verdierFixedRoofImageHomotopy i q x y
        (verdierLiftedIdentityConeImageHomotopy h x p U hU) := by
    rw [verdierFixedLiftedConeEvaluation, intervalFamilyOfEdge_homotopy,
      simplicialHomotopyOfFunctorEdge_of_homotopy]
  have hea := congrArg (fun J => J.h) ha
  change (β_ P (Δ[1] : SSet.{u})).hom ≫
      intervalMappingUncurry (verdierFixedLiftedConeEvaluation h x y p U hU) =
      (σ ▷ (Δ[1] : SSet.{u})) ≫ H.h ≫ p at hea
  have hn : leftIntervalCylinderSection K ≫ fatConeCylinderProjection K =
      (β_ (Δ[1] : SSet.{u}) K).hom := by
    apply SSet.hom_ext
    intro n
    rfl
  have hb : ((Δ[1] : SSet.{u}) ◁ σ) ≫ (β_ Δ[1] K).hom =
      (β_ (Δ[1] : SSet.{u}) P).hom ≫ (σ ▷ Δ[1]) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, leftIntervalFatPrism_naturality, Category.assoc]
  change (Δ[1] ◁ σ) ≫
      (leftIntervalCylinderSection K ≫ fatJoinCylinder Δ[0] K ≫ homotopyFatCone H) ≫ p = _
  rw [homotopyFatCone_cylinder, ← Category.assoc (leftIntervalCylinderSection K), hn,
    ← Category.assoc, ← Category.assoc, hb, Category.assoc, Category.assoc, ← hea,
    ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

private def verdierFixedLiftedCosliceEvaluation {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    fixedMarkedSpans B.obj (weakEquivalences i) x y ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)))
        (q.hom.app _ y) :=
  (verdierLiftedConeImageData h x p U hU).toFiber
    (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y)
    (fixedMarkedSpanToFamily_target q.hom (weakEquivalences i) x y)

private def verdierFixedLiftedCosliceHomotopy {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    SSet.Homotopy
      (verdierFixedLiftedCosliceEvaluation h x y p U hU ≫
        cosliceFiberToIntervalMappingSpace (q.hom.app _ x) (q.hom.app _ y))
      (verdierFixedLiftedConeEvaluation h x y p U hU) :=
  (verdierLiftedConeImageData h x p U hU).toFiberIntervalHomotopy
    (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y)
    (fixedMarkedSpanToFamily_target q.hom (weakEquivalences i) x y)
    (verdierFixedLiftedConeEvaluation h x y p U hU)
    (verdierLiftedConeImage_fixedPrism h x y p U hU)

private def verdierFixedLiftedCosliceIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    FunctorIso
      (verdierFixedLiftedCosliceEvaluation h x y p U hU ≫
        cosliceFiberToIntervalMappingSpace (q.hom.app _ x) (q.hom.app _ y))
      (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y) := by
  let H := verdierFixedLiftedCosliceHomotopy h x y p U hU
  haveI : IsIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj
      ((ihom (fixedMarkedSpans B.obj (weakEquivalences i) x y)).obj
        (intervalMappingSpace (q.hom.app _ x) (q.hom.app _ y)))) _
  exact asIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) ≪≫
    verdierFixedLiftedConeEvaluationIso h x y p U hU

private lemma verdierLiftedIdentityPointMap_eq {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x)) ≫ p =
      SSet.yonedaEquiv.symm (q.hom.app _ x) := by
  rw [SSet.yonedaEquiv_symm_comp, verdierLiftedIdentity_vertex_image h x p U hU]

private def verdierLiftedCosliceProjection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    sliceUnder (SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x))) ⟶
      sliceUnder (SSet.yonedaEquiv.symm (q.hom.app _ x)) :=
  sliceUnderPostcomp (SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x))) p ≫
    eqToHom (congrArg sliceUnder (verdierLiftedIdentityPointMap_eq h x p U hU))

private lemma verdierLiftedCosliceProjection_projection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    verdierLiftedCosliceProjection h x p U hU ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)) =
    sliceUnderProjection (SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x))) ≫ p := by
  rw [verdierLiftedCosliceProjection, Category.assoc,
    sliceUnder_eqToHom_projection (verdierLiftedIdentityPointMap_eq h x p U hU)]
  exact sliceUnderPostcomp_projection _ _

private lemma verdierLiftedCosliceProjection_trivialKan {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    TrivialKanFibration (verdierLiftedCosliceProjection h x p U hU) := by
  constructor
  exact trivialKanFibrations.comp_mem _ _
    (sliceUnderPostcomp_trivialKanFibration
      (SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x))) p).mem
    (MorphismProperty.rlp_of_isIso _ _)

private def verdierFixedLiftedConeTotal {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    fixedMarkedSpans B.obj (weakEquivalences i) x y ⟶
      leftFibrationInitialTotal p (U.app _ (verdierIdentitySpanFamily h x)) (q.hom.app _ y) :=
  vertexFiberLift _ _
    (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y ≫
      verdierLiftedIdentityCoslice h x p U hU) (by
    rw [Category.assoc, ← Category.assoc (verdierLiftedIdentityCoslice h x p U hU),
      verdierLiftedIdentityCoslice_projection, hU,
      fixedMarkedSpanToFamily_target q.hom (weakEquivalences i) x y])

private def verdierFixedLiftedConeProjection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    leftFibrationInitialTotal p (U.app _ (verdierIdentitySpanFamily h x)) (q.hom.app _ y) ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) (q.hom.app _ y) :=
  vertexFiberMap _ _ (verdierLiftedCosliceProjection h x p U hU)
    (verdierLiftedCosliceProjection_projection h x p U hU) (q.hom.app _ y)

private lemma verdierFixedLiftedConeProjection_trivialKan {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    TrivialKanFibration (verdierFixedLiftedConeProjection h x y p U hU) := by
  letI := verdierLiftedCosliceProjection_trivialKan h x p U hU
  exact HomotopyLimits.vertexFiberMap_trivialKanFibration _ _ _ _ _

private lemma verdierFixedLiftedConeTotal_projection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    verdierFixedLiftedConeTotal h x y p U hU ≫ verdierFixedLiftedConeProjection h x y p U hU =
      verdierFixedLiftedCosliceEvaluation h x y p U hU := by
  apply vertexFiber_hom_ext _ _
  rw [Category.assoc, verdierFixedLiftedConeProjection, vertexFiberMap_ι,
    ← Category.assoc, verdierFixedLiftedConeTotal, vertexFiberLift_ι]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change ((eqToHom (congrArg sliceUnder (verdierLiftedIdentityPointMap_eq h x p U hU))).app
    (Opposite.op ⦋n⦌) _).val = _
  rw [sliceUnder_eqToHom_app_val (verdierLiftedIdentityPointMap_eq h x p U hU)]
  rfl

private def verdierFixedLiftedFamily {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    fixedMarkedSpans B.obj (weakEquivalences i) x y ⟶ vertexFiber p (q.hom.app _ y) :=
  vertexFiberLift _ _ (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y ≫ U) (by
    rw [Category.assoc, hU, fixedMarkedSpanToFamily_target q.hom (weakEquivalences i) x y])

private lemma verdierFixedLiftedConeTotal_evaluation {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    verdierFixedLiftedConeTotal h x y p U hU ≫
      leftFibrationInitialEvaluation p (U.app _ (verdierIdentitySpanFamily h x))
        (q.hom.app _ y) = verdierFixedLiftedFamily h x y p U hU := by
  apply vertexFiber_hom_ext p (q.hom.app _ y)
  rw [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι,
    ← Category.assoc, verdierFixedLiftedConeTotal, vertexFiberLift_ι,
    verdierFixedLiftedFamily, vertexFiberLift_ι, Category.assoc,
    verdierLiftedIdentityCoslice_projection]

private def verdierFixedLiftedBaseEquivalence {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    QCatEquivalence
      (leftFibrationInitialTotal p (U.app _ (verdierIdentitySpanFamily h x)) (q.hom.app _ y))
      (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)))
        (q.hom.app _ y)) := by
  letI := vertexFiber_kanComplex_of_leftFibration
    (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) (q.hom.app _ y)
  letI := verdierFixedLiftedConeProjection_trivialKan h x y p U hU
  exact qCatEquivalenceOfTrivialKanFibration (verdierFixedLiftedConeProjection h x y p U hU)

private def verdierFixedLiftedNativeComparison {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)))
      (q.hom.app _ y) ⟶ vertexFiber p (q.hom.app _ y) :=
  (verdierFixedLiftedBaseEquivalence h x y p U hU).inv ≫
    leftFibrationInitialEvaluation p (U.app _ (verdierIdentitySpanFamily h x)) (q.hom.app _ y)

private def verdierFixedLiftedNativeTriangle {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    FunctorIso
      (verdierFixedLiftedCosliceEvaluation h x y p U hU ≫
        verdierFixedLiftedNativeComparison h x y p U hU)
      (verdierFixedLiftedFamily h x y p U hU) := by
  let e := verdierFixedLiftedBaseEquivalence h x y p U hU
  let φ := verdierFixedLiftedConeTotal h x y p U hU
  let ev := leftFibrationInitialEvaluation p
    (U.app _ (verdierIdentitySpanFamily h x)) (q.hom.app _ y)
  have ht := FunctorIso.postcomp (FunctorIso.precomp e.homInvIso φ) ev
  change FunctorIso
    ((φ ≫ (verdierFixedLiftedConeProjection h x y p U hU ≫ e.inv)) ≫ ev)
    ((φ ≫ 𝟙 _) ≫ ev) at ht
  have ht' : FunctorIso
      ((verdierFixedLiftedConeTotal h x y p U hU ≫
        verdierFixedLiftedConeProjection h x y p U hU) ≫
          verdierFixedLiftedNativeComparison h x y p U hU)
      (verdierFixedLiftedConeTotal h x y p U hU ≫ ev) := by
    simpa only [verdierFixedLiftedNativeComparison, φ, e, ev,
      Category.assoc, Category.comp_id] using ht
  rw [verdierFixedLiftedConeTotal_projection, verdierFixedLiftedConeTotal_evaluation] at ht'
  exact ht'

private def verdierFixedIntervalBaseEquivalence {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) :
    QCatEquivalence
      (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)))
        (q.hom.app _ y))
      (intervalMappingSpace (q.hom.app _ x) (q.hom.app _ y)) := by
  letI := vertexFiber_kanComplex_of_leftFibration
    (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) (q.hom.app _ y)
  exact (cosliceFiberToIntervalMappingSpace_isQCatEquivalence
    (q.hom.app _ x) (q.hom.app _ y)).choose

private def verdierFixedLiftedIntervalComparison {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    intervalMappingSpace (q.hom.app _ x) (q.hom.app _ y) ⟶ vertexFiber p (q.hom.app _ y) :=
  (verdierFixedIntervalBaseEquivalence h x y).inv ≫
    verdierFixedLiftedNativeComparison h x y p U hU

private def verdierFixedLiftedIntervalTriangle {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    FunctorIso
      (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y ≫
        verdierFixedLiftedIntervalComparison h x y p U hU)
      (verdierFixedLiftedFamily h x y p U hU) := by
  let d := verdierFixedLiftedCosliceEvaluation h x y p U hU
  let e := verdierFixedIntervalBaseEquivalence h x y
  let b := verdierFixedLiftedNativeComparison h x y p U hU
  have h₁ := FunctorIso.postcomp (verdierFixedLiftedCosliceIso h x y p U hU).symm
    (verdierFixedLiftedIntervalComparison h x y p U hU)
  have h₂ := FunctorIso.postcomp (FunctorIso.precomp e.homInvIso d) b
  have h₃ := verdierFixedLiftedNativeTriangle h x y p U hU
  have he : FunctorIso ((d ≫ e.hom) ≫ (e.inv ≫ b)) (d ≫ b) := by
    simpa only [Category.assoc, Category.comp_id] using h₂
  exact h₁ ≪≫ he ≪≫ h₃

private def verdierFixedLiftedCompletion {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y) ⟶
      vertexFiber p (q.hom.app _ y) := by
  letI := vertexFiber_kanComplex_of_leftFibration p (q.hom.app _ y)
  exact groupoidCompletionEvaluation (verdierFixedLiftedFamily h x y p U hU)

private def verdierFixedLiftedCompletionTriangle {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    FunctorIso
      (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y ≫
        verdierFixedLiftedIntervalComparison h x y p U hU)
      (verdierFixedLiftedCompletion h x y p U hU) := by
  letI := vertexFiber_kanComplex_of_leftFibration p (q.hom.app _ y)
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization _)
  have he := FunctorIso.postcomp
      (fractionMappingComparisonIso q.hom (weakEquivalences i) h.inverts x y)
      (verdierFixedLiftedIntervalComparison h x y p U hU) ≪≫
    verdierFixedLiftedIntervalTriangle h x y p U hU ≪≫
      (groupoidCompletionEvaluationIso (verdierFixedLiftedFamily h x y p U hU)).symm
  simpa only [verdierFixedLiftedCompletion, Category.assoc] using he

private lemma verdierLiftedCosliceProjection_identity {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    (verdierLiftedCosliceProjection h x p U hU).app _
      (cosliceIdentityCone (U.app _ (verdierIdentitySpanFamily h x))) =
      cosliceIdentityCone (q.hom.app _ x) := by
  apply Subtype.ext
  change ((eqToHom (congrArg sliceUnder (verdierLiftedIdentityPointMap_eq h x p U hU))).app
    (Opposite.op ⦋0⦌) _).val = _
  rw [sliceUnder_eqToHom_app_val (verdierLiftedIdentityPointMap_eq h x p U hU)]
  change SSet.const (U.app _ (verdierIdentitySpanFamily h x)) ≫ p = SSet.const (q.hom.app _ x)
  rw [SSet.const_comp, verdierLiftedIdentity_vertex_image h x p U hU]

private lemma exists_verdierLiftedCosliceSection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    ∃ s : sliceUnder (SSet.yonedaEquiv.symm (q.hom.app _ x)) ⟶
        sliceUnder (SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x))),
      s ≫ verdierLiftedCosliceProjection h x p U hU = 𝟙 _ ∧
      s.app _ (cosliceIdentityCone (q.hom.app _ x)) =
        cosliceIdentityCone (U.app _ (verdierIdentitySpanFamily h x)) := by
  let a := SSet.yonedaEquiv.symm
    (cosliceIdentityCone (U.app _ (verdierIdentitySpanFamily h x)))
  let b := SSet.yonedaEquiv.symm (cosliceIdentityCone (q.hom.app _ x))
  haveI : Mono b := by
    rw [NatTrans.mono_iff_mono_app]
    rintro ⟨⟨n⟩⟩
    rw [mono_iff_injective]
    intro v w _
    apply SSet.stdSimplex.ext
    intro j
    apply Fin.ext
    omega
  have := (verdierLiftedCosliceProjection_trivialKan h x p U hU).mem b inferInstance
  let sq : CommSq a b (verdierLiftedCosliceProjection h x p U hU) (𝟙 _) := by
    constructor
    change a ≫ verdierLiftedCosliceProjection h x p U hU = b ≫ 𝟙 _
    rw [Category.comp_id, SSet.yonedaEquiv_symm_comp,
      verdierLiftedCosliceProjection_identity h x p U hU]
  refine ⟨sq.lift, sq.fac_right, ?_⟩
  have hs := congrArg SSet.yonedaEquiv sq.fac_left
  simpa only [a, b, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hs

private def verdierLiftedCosliceSection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :=
  (exists_verdierLiftedCosliceSection h x p U hU).choose

private lemma verdierLiftedCosliceSection_projection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    verdierLiftedCosliceSection h x p U hU ≫ verdierLiftedCosliceProjection h x p U hU = 𝟙 _ :=
  (exists_verdierLiftedCosliceSection h x p U hU).choose_spec.1

private lemma verdierLiftedCosliceSection_identity {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    (verdierLiftedCosliceSection h x p U hU).app _ (cosliceIdentityCone (q.hom.app _ x)) =
      cosliceIdentityCone (U.app _ (verdierIdentitySpanFamily h x)) :=
  (exists_verdierLiftedCosliceSection h x p U hU).choose_spec.2

private def verdierLiftedCosliceSectionEvaluation {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    sliceUnder (SSet.yonedaEquiv.symm (q.hom.app _ x)) ⟶ E :=
  verdierLiftedCosliceSection h x p U hU ≫
    sliceUnderProjection (SSet.yonedaEquiv.symm (U.app _ (verdierIdentitySpanFamily h x)))

private lemma verdierLiftedCosliceSectionEvaluation_projection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    verdierLiftedCosliceSectionEvaluation h x p U hU ≫ p =
      sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)) := by
  rw [verdierLiftedCosliceSectionEvaluation, Category.assoc,
    ← verdierLiftedCosliceProjection_projection h x p U hU,
    ← Category.assoc, verdierLiftedCosliceSection_projection, Category.id_comp]

private lemma verdierLiftedCosliceSectionEvaluation_identity {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    (verdierLiftedCosliceSectionEvaluation h x p U hU).app _
      (cosliceIdentityCone (q.hom.app _ x)) = U.app _ (verdierIdentitySpanFamily h x) := by
  change (sliceUnderProjection _).app _
    ((verdierLiftedCosliceSection h x p U hU).app _ (cosliceIdentityCone (q.hom.app _ x))) = _
  rw [verdierLiftedCosliceSection_identity, cosliceIdentityCone_projection]

private def verdierLiftedIdentityFiberPoint {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    (vertexFiber p (q.hom.app _ x)) _⦋0⦌ :=
  ⟨U.app _ (verdierIdentitySpanFamily h x), by
    rw [pinchedConstant_zero]
    exact verdierLiftedIdentity_vertex_image h x p U hU⟩

private def verdierLiftedCosliceSectionEvaluation_relativeIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    VertexIso
      (relativeFunctorVertex p (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)))
        (verdierLiftedCosliceSectionEvaluation h x p U hU)
        (verdierLiftedCosliceSectionEvaluation_projection h x p U hU))
      (relativeFunctorVertex p (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)))
        (coslicePointFamilyAt p (q.hom.app _ x) (verdierLiftedIdentityFiberPoint h x p U hU))
        (coslicePointFamilyAt_projection p (q.hom.app _ x) _)) := by
  apply coslicePointEvaluation_relativeIso p (q.hom.app _ x)
    (verdierLiftedCosliceSectionEvaluation_projection h x p U hU)
    (coslicePointFamilyAt_projection p (q.hom.app _ x) _)
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  apply Subtype.ext
  rw [coslicePointEvaluation_vertex_val p (q.hom.app _ x),
    coslicePointEvaluation_vertex_val p (q.hom.app _ x),
    verdierLiftedCosliceSectionEvaluation_identity, coslicePointFamilyAt_identity]
  rfl

private def verdierFixedLiftedCosliceSection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)))
      (q.hom.app _ y) ⟶
    leftFibrationInitialTotal p (U.app _ (verdierIdentitySpanFamily h x)) (q.hom.app _ y) :=
  vertexFiberMap _ _ (verdierLiftedCosliceSection h x p U hU)
    (by simpa only [verdierLiftedCosliceSectionEvaluation, Category.assoc] using
      verdierLiftedCosliceSectionEvaluation_projection h x p U hU) (q.hom.app _ y)

private lemma verdierFixedLiftedCosliceSection_projection {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    verdierFixedLiftedCosliceSection h x y p U hU ≫
      verdierFixedLiftedConeProjection h x y p U hU = 𝟙 _ := by
  apply vertexFiber_hom_ext _ _
  rw [Category.assoc, verdierFixedLiftedConeProjection, vertexFiberMap_ι,
    ← Category.assoc, verdierFixedLiftedCosliceSection, vertexFiberMap_ι,
    Category.assoc, verdierLiftedCosliceSection_projection,
    Category.comp_id, Category.id_comp]

private lemma verdierFixedLiftedCosliceSection_evaluation {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    verdierFixedLiftedCosliceSection h x y p U hU ≫
      leftFibrationInitialEvaluation p (U.app _ (verdierIdentitySpanFamily h x))
        (q.hom.app _ y) =
    vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) p
      (verdierLiftedCosliceSectionEvaluation h x p U hU)
      (verdierLiftedCosliceSectionEvaluation_projection h x p U hU) (q.hom.app _ y) := by
  rw [verdierFixedLiftedCosliceSection, leftFibrationInitialEvaluation, vertexFiberMap_comp]
  rfl

private def verdierFixedLiftedNativePointIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) :
    FunctorIso (verdierFixedLiftedNativeComparison h x y p U hU)
      (vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) p
        (coslicePointFamilyAt p (q.hom.app _ x) (verdierLiftedIdentityFiberPoint h x p U hU))
        (coslicePointFamilyAt_projection p (q.hom.app _ x) _) (q.hom.app _ y)) := by
  let e := verdierFixedLiftedBaseEquivalence h x y p U hU
  let s := verdierFixedLiftedCosliceSection h x y p U hU
  let ev := leftFibrationInitialEvaluation p
    (U.app _ (verdierIdentitySpanFamily h x)) (q.hom.app _ y)
  have he := FunctorIso.precomp e.homInvIso s
  change FunctorIso (s ≫ (verdierFixedLiftedConeProjection h x y p U hU ≫ e.inv))
    (s ≫ 𝟙 _) at he
  rw [← Category.assoc, verdierFixedLiftedCosliceSection_projection,
    Category.id_comp, Category.comp_id] at he
  have ht := FunctorIso.postcomp he ev
  rw [verdierFixedLiftedCosliceSection_evaluation] at ht
  have hr := VertexIso.map (verdierLiftedCosliceSectionEvaluation_relativeIso h x p U hU)
    (relativeFunctorFiberHom
      (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) p (q.hom.app _ y))
  rw [relativeFunctorFiberHom_vertex, relativeFunctorFiberHom_vertex] at hr
  exact ht ≪≫ hr

private def verdierFixedLiftedNativeSpecifiedPointIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
    (w : (vertexFiber p (q.hom.app _ x)) _⦋0⦌)
    (e : VertexIso (verdierLiftedIdentityFiberPoint h x p U hU) w) :
    FunctorIso (verdierFixedLiftedNativeComparison h x y p U hU)
      (vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) p
        (coslicePointFamilyAt p (q.hom.app _ x) w)
        (coslicePointFamilyAt_projection p (q.hom.app _ x) w) (q.hom.app _ y)) := by
  let v := verdierLiftedIdentityFiberPoint h x p U hU
  have hv : (leftFibrationCoslicePointEvaluate p (q.hom.app _ x)).app _
      (relativeFunctorVertex p _ (coslicePointFamilyAt p (q.hom.app _ x) v)
        (coslicePointFamilyAt_projection p (q.hom.app _ x) v)) = v := by
    apply Subtype.ext
    exact (coslicePointEvaluation_vertex_val p (q.hom.app _ x) _).trans
      (coslicePointFamilyAt_identity p (q.hom.app _ x) v)
  have hw : (leftFibrationCoslicePointEvaluate p (q.hom.app _ x)).app _
      (relativeFunctorVertex p _ (coslicePointFamilyAt p (q.hom.app _ x) w)
        (coslicePointFamilyAt_projection p (q.hom.app _ x) w)) = w := by
    apply Subtype.ext
    exact (coslicePointEvaluation_vertex_val p (q.hom.app _ x) _).trans
      (coslicePointFamilyAt_identity p (q.hom.app _ x) w)
  have hr := coslicePointEvaluation_relativeIso p (q.hom.app _ x)
    (coslicePointFamilyAt_projection p (q.hom.app _ x) v)
    (coslicePointFamilyAt_projection p (q.hom.app _ x) w)
    (eqToIso (congrArg HomotopyCategory.mk hv) ≪≫ e ≪≫
      eqToIso (congrArg HomotopyCategory.mk hw.symm))
  have hf := VertexIso.map hr (relativeFunctorFiberHom
    (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) p (q.hom.app _ y))
  rw [relativeFunctorFiberHom_vertex, relativeFunctorFiberHom_vertex] at hf
  exact verdierFixedLiftedNativePointIso h x y p U hU ≪≫ hf

private def verdierFixedLiftedSpecifiedPointTriangle {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ C.obj) [LeftFibration p]
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶ E)
    (hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
    (w : (vertexFiber p (q.hom.app _ x)) _⦋0⦌)
    (e : VertexIso (verdierLiftedIdentityFiberPoint h x p U hU) w) :
    FunctorIso
      (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y ≫
        ((verdierFixedIntervalBaseEquivalence h x y).inv ≫
          vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))) p
            (coslicePointFamilyAt p (q.hom.app _ x) w)
            (coslicePointFamilyAt_projection p (q.hom.app _ x) w) (q.hom.app _ y)))
      (verdierFixedLiftedCompletion h x y p U hU) := by
  have he := FunctorIso.precomp
    (FunctorIso.precomp (verdierFixedLiftedNativeSpecifiedPointIso h x y p U hU w e)
      (verdierFixedIntervalBaseEquivalence h x y).inv)
    (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)
  exact he.symm ≪≫ verdierFixedLiftedCompletionTriangle h x y p U hU

private def verdierWeakQuotientUnitTriangle {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌)
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶
      smallLeftUnstraightening (weakSpanKanQuotientDiagram h x))
    (hU : U ≫ smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
      markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
    (e : VertexIso
      (verdierLiftedIdentityFiberPoint h x
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU)
      (weakIdentityQuotientFiberPoint h x)) :
    FunctorIso
      (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y ≫
        ((verdierFixedIntervalBaseEquivalence h x y).inv ≫
          vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x)))
            (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
            (weakQuotientCosliceUnit h x) (weakQuotientCosliceUnit_projection h x)
            (q.hom.app _ y)))
      (verdierFixedLiftedCompletion h x y
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU) := by
  simpa only [coslicePointFamilyAt, weakQuotientCosliceUnit] using
    verdierFixedLiftedSpecifiedPointTriangle h x y
      (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU
      (weakIdentityQuotientFiberPoint h x) e

private lemma verdierFractionComparison_of_wholeFamilyUnit {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌)
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶
      smallLeftUnstraightening (weakSpanKanQuotientDiagram h x))
    (hU : U ≫ smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
      markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
    (e : VertexIso
      (verdierLiftedIdentityFiberPoint h x
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU)
      (weakIdentityQuotientFiberPoint h x))
    (hunit : IsQCatEquivalence (verdierFixedLiftedCompletion h x y
      (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU)) :
    IsFullyFaithful (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y) := by
  let a := sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app _ x))
  let p := smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram a)
  let u := weakQuotientCosliceUnit h x
  let c := weakQuotientCosliceComparison h x
  let b := q.hom.app (Opposite.op ⦋0⦌) y
  let uf := vertexFiberMap a p u (weakQuotientCosliceUnit_projection h x) b
  let cf := vertexFiberMap p r c (weakQuotientCosliceComparison_projection h x) b
  let β := (verdierFixedIntervalBaseEquivalence h x y).inv ≫ uf
  letI := vertexFiber_kanComplex_of_leftFibration a b
  letI := vertexFiber_kanComplex_of_leftFibration p b
  letI := vertexFiber_kanComplex_of_leftFibration r b
  have hfg : IsQCatEquivalence
      (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y ≫ β) :=
    hunit.ofFunctorIso (verdierWeakQuotientUnitTriangle h x y U hU e).symm
  have huc : IsQCatEquivalence (uf ≫ cf) := by
    rw [vertexFiberMap_comp]
    exact vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence a r
      (weakQuotientCosliceComposite h x) (weakQuotientCosliceComposite_projection h x)
      (weakCosliceComposite_isPrecompositionEquivalence h x) b
  have hβc : IsQCatEquivalence (β ≫ cf) := by
    change IsQCatEquivalence
      (((verdierFixedIntervalBaseEquivalence h x y).inv ≫ uf) ≫ cf)
    rw [Category.assoc]
    exact (verdierFixedIntervalBaseEquivalence h x y).symm.isQCatEquivalence.comp huc
  have hβ : IsQCatEquivalence β := isQCatEquivalence_of_composites hfg hβc
  exact (hβ.cancel_right hfg).isFullyFaithful

private def verdierWeakFiberGroupoidEquivalence {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) :
    QCatEquivalence
      (vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app _ y))
      (groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y)) := by
  let c := transportSimplexIndex (n := ⦋0⦌) y
  let K := (weakSpanKanDiagram i x).obj c
  let F := weakSpanKanQuotientDiagram h x
  letI := vertexFiber_kanComplex_of_leftFibration (smallLeftUnstraighteningProjection F)
    (q.hom.app _ y)
  have hv : VertexIso (F.app (Opposite.op ⦋0⦌) (ULift.up (q.hom.app _ y)))
      (spaceInfinityVertex K) := by
    have hi := weakSpanKanQuotientDiagram_initialVertexIso h x c
    simpa only [c, transportSimplexFirstVertexMap_zeroIndex] using hi
  let a := (homotopyCategory_homMk_surjective _ _ hv.hom).choose
  have ha : Truncated.HomotopyCategory.homMk a = hv.hom :=
    (homotopyCategory_homMk_surjective _ _ hv.hom).choose_spec
  haveI : IsIso (Truncated.HomotopyCategory.homMk a) := by
    rw [ha]
    infer_instance
  have he : IsInvertibleEdge (SSet.Edge.ofTruncated a) := by
    change IsIso (Truncated.HomotopyCategory.homMk a)
    infer_instance
  let e := (F2.Compact.spaceInfinityEdgeValue_isQCatEquivalence
    (SSet.Edge.ofTruncated a) he).choose
  let eK := qCatEquivalenceOfIso (eqToIso
    (congrArg KanObject.obj (spaceInfinityVertexEquiv.left_inv K)))
  let eg := weakSpanKanValueGroupoidEquivalence i x c
  let ey := qCatEquivalenceOfIso (eqToIso
    (congrArg (fun z => groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x z))
      (transportSimplexFirstVertexMap_zeroIndex y)))
  exact ((smallLeftUnstraighteningFiberValueEquivalence F (q.hom.app _ y)).trans e).trans
    (eK.trans (eg.trans ey))

private lemma verdierFractionComparison_of_wholeFamilyRecovery {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌)
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶
      smallLeftUnstraightening (weakSpanKanQuotientDiagram h x))
    (hU : U ≫ smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
      markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
    (e : VertexIso
      (verdierLiftedIdentityFiberPoint h x
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU)
      (weakIdentityQuotientFiberPoint h x))
    (hrecovery : FunctorIso
      (verdierFixedLiftedFamily h x y
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU ≫
          (verdierWeakFiberGroupoidEquivalence h x y).hom)
      (groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y))) :
    IsFullyFaithful (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y) := by
  let p := smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)
  letI := vertexFiber_kanComplex_of_leftFibration p (q.hom.app _ y)
  have he : FunctorIso
      (verdierFixedLiftedCompletion h x y p U hU ≫
        (verdierWeakFiberGroupoidEquivalence h x y).hom)
      (𝟙 (groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y))) := by
    apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization _)
    have ht := FunctorIso.postcomp
      (groupoidCompletionEvaluationIso (verdierFixedLiftedFamily h x y p U hU))
      (verdierWeakFiberGroupoidEquivalence h x y).hom ≪≫ hrecovery
    simpa only [verdierFixedLiftedCompletion, Category.assoc, Category.comp_id] using ht
  have hc : IsQCatEquivalence
      (verdierFixedLiftedCompletion h x y p U hU ≫
        (verdierWeakFiberGroupoidEquivalence h x y).hom) :=
    (QCatEquivalence.refl _).isQCatEquivalence.ofFunctorIso he.symm
  have hu : IsQCatEquivalence (verdierFixedLiftedCompletion h x y p U hU) :=
    (verdierWeakFiberGroupoidEquivalence h x y).isQCatEquivalence.cancel_right hc
  exact verdierFractionComparison_of_wholeFamilyUnit h x y U hU e hu

/-- 元の全族の実 Kan 単位回収を、既存の亜群化比較を介して私有判定へ渡す。 -/
private lemma verdierFractionComparison_of_kanUnitRecovery {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌)
    (U : markedSpanFamily B.obj (weakEquivalences i) x ⟶
      smallLeftUnstraightening (weakSpanKanQuotientDiagram h x))
    (hU : U ≫ smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
      markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
    (e : VertexIso
      (verdierLiftedIdentityFiberPoint h x
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU)
      (weakIdentityQuotientFiberPoint h x))
    (v : vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
      (q.hom.app _ y) ⟶ (strictKanCompletion.obj
        (fixedMarkedSpans B.obj (weakEquivalences i) x y)).obj)
    (hv : IsQCatEquivalence v)
    (hrecovery : FunctorIso
      (verdierFixedLiftedFamily h x y
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)) U hU ≫ v)
      (F2.continuousKanReplacementUnit.app (fixedMarkedSpans B.obj (weakEquivalences i) x y))) :
    IsFullyFaithful (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y) := by
  let p := smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)
  let X := fixedMarkedSpans B.obj (weakEquivalences i) x y
  letI := vertexFiber_kanComplex_of_leftFibration p (q.hom.app _ y)
  have he : FunctorIso
      (verdierFixedLiftedCompletion h x y p U hU ≫ v)
      (groupoidCompletionKanComparison X) := by
    apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization X)
    have ht := (groupoidCompletionEvaluationIso
      (verdierFixedLiftedFamily h x y p U hU)).postcomp v ≪≫ hrecovery ≪≫
        (groupoidCompletionEvaluationIso (F2.continuousKanReplacementUnit.app X)).symm
    simpa only [verdierFixedLiftedCompletion, groupoidCompletionKanComparison,
      Category.assoc] using! ht
  have hc := (groupoidCompletionKanComparison_isQCatEquivalence X).ofFunctorIso he.symm
  exact verdierFractionComparison_of_wholeFamilyUnit h x y U hU e (hv.cancel_right hc)

/-- 概要：元の一般 Verdier 分数比較は全写像空間で充満忠実。
方針：実全族写像・同じ底・全固定 fiber の Kan 単位回収・元の恒等点照合を適用する。
規約：全族単位や fiber 同値を追加入力にしない。
使われ方：K-B の分数比較と K-S• の再開条件。 -/
lemma verdierFractionMappingComparison_isFullyFaithful {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) :
    IsFullyFaithful (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y) := by
  let p := smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)
  let U := weakSpanKanQuotientFamilyMap h x
  have hU : U ≫ p = markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom :=
    weakSpanKanQuotientFamilyMap_projection h x
  have hi : verdierLiftedIdentityFiberPoint h x p U hU =
      (weakSpanKanQuotientFamilyFixedFiber h x x).app (Opposite.op ⦋0⦌)
        (weakIdentityFixedSpan h x) := by
    apply Subtype.ext
    change U.app _ (verdierIdentitySpanFamily h x) =
      U.app _ ((fixedMarkedSpanToFamily B.obj (weakEquivalences i) x x).app _
        (weakIdentityFixedSpan h x))
    congr 1
  let e : VertexIso (verdierLiftedIdentityFiberPoint h x p U hU)
      (weakIdentityQuotientFiberPoint h x) :=
    eqToIso (congrArg HomotopyCategory.mk hi) ≪≫
      weakSpanKanQuotientFamilyFixedFiber_identityIso h x
  apply verdierFractionComparison_of_kanUnitRecovery h x y U hU e
    (weakSpanKanQuotientZeroValueComparison h x y)
    (weakSpanKanQuotientZeroValueComparison_isQCatEquivalence h x y)
  simpa only [verdierFixedLiftedFamily, weakSpanKanQuotientFamilyFixedFiber] using!
    weakSpanKanQuotientFamilyFixedFiber_recovery h x y

end SerrePositivity.KST.LocalizingInvariants
