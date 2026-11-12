module

public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonHomSquares

/-!
概要：元の錐の比較三単体の四頂点と中央 Hom を、元の BF 対象と全 Hom に厳密同定する。
方針：元の apex 辺と底の区間の等式を、coherent 単体の対象で評価する。
規約：頂点を単なる同値で置換しない。使われ方：元の比較正方形の零辺と前合成の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleComparisonCellObjectsSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の比較三単体の最後の辺は、元の一点からの厳密射の同じ coherent 辺。 -/
lemma circleCompanionComparisonTetrahedron_base_fromPoint (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 2 3 (by decide)) ≫
      SSet.yonedaEquiv.symm (circleCompanionComparisonTetrahedron z k) =
    SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val)).edge := by
  rw [circleCompanionComparisonTetrahedron_base]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    circleConeComparisonParameter, Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum.{u}).app (Opposite.op ⦋1⦌) _ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum.{u}).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ (fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val))
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum.{u}).app (Opposite.op ⦋1⦌))
  cases k
  all_goals
    refine ComposableArrows.ext₁ rfl rfl ?_
    change fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val = _
    simp

/-- 元の三単体の最初の頂点は、元の円 cotensor。 -/
lemma circleCompanionComparisonTetrahedron_obj_zero (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    (circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 0⟩ =
      cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val := by
  have h := congrArg SSet.yonedaEquiv (circleCompanionComparisonTetrahedron_apex z k)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact congrArg (fun s : Sp.{u} _⦋1⦌ ↦ s.obj ⟨ULift.up 0⟩) h

/-- 元の三単体の二番目の頂点も、同じ元の円 cotensor。 -/
lemma circleCompanionComparisonTetrahedron_obj_one (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    (circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 1⟩ =
      cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val := by
  have h := congrArg SSet.yonedaEquiv (circleCompanionComparisonTetrahedron_apex z k)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact congrArg (fun s : Sp.{u} _⦋1⦌ ↦ s.obj ⟨ULift.up 1⟩) h

/-- 元の三単体の三番目の頂点は、元の一点 BF スペクトル。 -/
lemma circleCompanionComparisonTetrahedron_obj_two (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    (circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 2⟩ = _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint := by
  have h := congrArg SSet.yonedaEquiv
    (circleCompanionComparisonTetrahedron_base_fromPoint z k)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact congrArg (fun s : Sp.{u} _⦋1⦌ ↦ s.obj ⟨ULift.up 0⟩) h

/-- 元の三単体の最後の頂点は、元の入力 BF スペクトル。 -/
lemma circleCompanionComparisonTetrahedron_obj_three (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    (circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 3⟩ =
      (nativeCotensorInput PointedSimplicialSet.circle z).val := by
  have h := congrArg SSet.yonedaEquiv
    (circleCompanionComparisonTetrahedron_base_fromPoint z k)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact congrArg (fun s : Sp.{u} _⦋1⦌ ↦ s.obj ⟨ULift.up 1⟩) h

/-- 共通の中央 Hom は、元の円 cotensor から元の入力への全 Hom そのもの。 -/
lemma circleComparisonCentralHom_eq (z : Sp.{u} _⦋0⦌) :
    circleComparisonCentralHom z = (circleEvaluationPointedHom z).right := by
  have h := congrArg (fun s : Sp.{u} _⦋2⦌ ↦
    SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
      (circleCompanionComparisonTetrahedron_two z .left)
  change SimplicialCategory.sHom
    ((circleCompanionComparisonTetrahedron z .left).obj ⟨ULift.up 0⟩)
    ((circleCompanionComparisonTetrahedron z .left).obj ⟨ULift.up 3⟩) =
      circleComparisonCentralHom z at h
  rw [circleCompanionComparisonTetrahedron_obj_zero,
    circleCompanionComparisonTetrahedron_obj_three] at h
  exact h.symm

/-- 元の二つの比較正方形を、同じ元の全 Hom 内へ厳密に表示する。 -/
def circleCompanionComparisonRawHomSquare (z : Sp.{u} _⦋0⦌) (k : Limits.WalkingPair) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (circleEvaluationPointedHom z).right :=
  circleCompanionComparisonHomSquare z k ≫ eqToHom (circleComparisonCentralHom_eq z)

end SerrePositivity.KST.Spectra.OmegaSpectrum
