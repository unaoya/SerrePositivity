module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKMap
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorExact
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition

/-!
概要：元の cone からの商射と同じ実懸垂入力射の四角形を、全関手同型で照合する。
方針：実増大への前合成で、元の二つの商屋根と厳密射影四角形へ戻して反映する。
規約：同じ augmentation と同じ商入力射を保持し、分解の逆を選び直さない。
使われ方：K-7 e の実懸垂 Morita 同値を、元の同じ厳密 dg 入力射へ結び付ける。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
  (M : DGKappaSuspensionMapData R C D I J)

/-- 元の商射・cone 射と、元の厳密な実懸垂入力射を結ぶ全関手四角形。 -/
def dgKappaSuspensionProjectionNaturality :
    FunctorIso (dgKappaSuspensionProjection R C I ≫
      dgNerve.map (dgKappaSuspensionInputMap R C D I J M).down)
      (dgNerve.map M.cone ≫ dgKappaSuspensionProjection R D J) := by
  apply ((dgCellResolutionNerveEquivalence R (DGKappaCone R C I)).isQCatEquivalence.precompose
    (dgKappaSuspensionInfinity R D J)).isFullyFaithful.preimageVertexIso
  have ha := congrArg (fun F => dgNerve.map F) M.augmentation
  simp only [dgNerve.map_comp] at ha
  have hp := congrArg (fun k => dgNerve.map k.down)
    (dgKappaSuspensionInputMap_projection R C D I J M)
  change dgNerve.map ((dgKappaResolvedSuspensionInputMap R C I).down.comp
      (dgKappaSuspensionInputMap R C D I J M).down) =
    dgNerve.map (M.resolved.comp (dgKappaResolvedSuspensionInputMap R D J).down) at hp
  simp only [dgNerve.map_comp] at hp
  have h₀ := (resolvedDGQuotientRoofIso R (DGKappaCone R C I)
    (dgKappaConePerfectObjects R C I)).postcomp
      (dgNerve.map (dgKappaSuspensionInputMap R C D I J M).down)
  have h₁ := (resolvedDGQuotientRoofIso R (DGKappaCone R D J)
    (dgKappaConePerfectObjects R D J)).precomp (dgNerve.map M.resolved)
  change FunctorIso
    ((dgNerve.map M.resolved ≫
      dgNerve.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D J))) ≫
        dgKappaSuspensionProjection R D J)
    (dgNerve.map M.resolved ≫
      dgNerve.map (dgKappaResolvedSuspensionInputMap R D J).down) at h₁
  rw [ha] at h₁
  change FunctorIso
    (dgNerve.map (DGCategoryCellResolution.augmentation R (DGKappaCone R C I)) ≫
      (dgNerve.map M.cone ≫ dgKappaSuspensionProjection R D J))
    (dgNerve.map M.resolved ≫
      dgNerve.map (dgKappaResolvedSuspensionInputMap R D J).down) at h₁
  change FunctorIso
    (dgNerve.map (DGCategoryCellResolution.augmentation R (DGKappaCone R C I)) ≫
      (dgKappaSuspensionProjection R C I ≫
        dgNerve.map (dgKappaSuspensionInputMap R C D I J M).down))
    (dgNerve.map (dgKappaResolvedSuspensionInputMap R C I).down ≫
      dgNerve.map (dgKappaSuspensionInputMap R C D I J M).down) at h₀
  rw [hp] at h₀
  exact h₀ ≪≫ h₁.symm

/-- 元の実懸垂入力射は、同じ実商の間の完全関手を誘導する。 -/
theorem dgKappaSuspensionInputMap_isExact :
    IsExactFunctor (dgNerve.map (dgKappaSuspensionInputMap R C D I J M).down) := by
  let : IsDGPretriangulated R (dgKappaSuspensionKInput R C I) := by
    let := dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R C I)
    exact dgQuotient_isDGPretriangulated R _ _ (resolvedDGQuotient_localKFlat R _ _)
  let : IsDGPretriangulated R (dgKappaSuspensionKInput R D J) := by
    let := dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D J)
    exact dgQuotient_isDGPretriangulated R _ _ (resolvedDGQuotient_localKFlat R _ _)
  exact dgPretriangulatedFunctor_isExactFunctor R _ _ _

end SerrePositivity.KST.NonConnective
