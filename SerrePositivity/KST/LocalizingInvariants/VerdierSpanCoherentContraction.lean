module

public import SerrePositivity.KST.LocalizingInvariants.VerdierFractionComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMinimum
public import SerrePositivity.InfinityCategories.F1B.Diagrams.IntervalMaximum
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
public import SerrePositivity.KST.LocalizingInvariants.IntervalMarkedEdges
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor
public import SerrePositivity.KST.Fibration.IdentityMarkedSpan
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorCompositionRestriction
public import SerrePositivity.InfinityCategories.F1.Joins.HomotopyConeRealization

/-!
概要：一般 Verdier 分数の全族に対して、分母 roof からの二つの実変形を保持する。
方針：元の span の第一辺を保つ変形と、分母による恒等 span への変形を用いる。
規約：私有の構成段階。π₀ の比較だけで高次の充満忠実性を結論しない。
使われ方：Sp-6 s4 の左三角形の検証。
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

end SerrePositivity.KST.LocalizingInvariants
