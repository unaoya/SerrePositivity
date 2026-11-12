module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionEdgewiseSection
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.FramedTetrahedronDifference

/-!
概要：companion の元の共通解像の二つの三単体の、内辺・外辺・右辺を厳密に計算する。
方針：loop 係数の全切断の面の式と右射影の切断式を、同じ BK 初区間へ適用する。
規約：三単体は元の Hom 内にある。使われ方：反転錐の符号と頂点比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の companion の全解像切断を左右の初区間で読んだ、同じ Hom 内の三単体。 -/
def circleCompanionEdgewiseTetrahedron (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    (Δ[3] : SSet.{u}) ⟶ (circleEvaluationPointedHom z).right :=
  EdgewiseCoordinates.tetrahedronMap (SSet.yonedaEquiv
    (LoopEdgewiseSection.parameter (circleEvaluationPointedHom z)
      (circleCompanionBKEdgewiseLoopSection z) k))

/-- 各三単体の元の内辺は、同じ零 Hom 頂点で定値。 -/
lemma circleCompanionEdgewiseTetrahedron_inner (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 1 2 (by decide)) ≫
      circleCompanionEdgewiseTetrahedron z k =
        SSet.const (circleEvaluationPointedHom z).basepoint :=
  LoopEdgewiseSection.innerCurve_constant _ _ k

/-- 元の二つの三単体の外辺は、同じ中央の頂点の経路。 -/
lemma circleCompanionEdgewiseTetrahedron_outer (z : Sp.{u} _⦋0⦌) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 3 (by decide)) ≫
        circleCompanionEdgewiseTetrahedron z .left =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 3 (by decide)) ≫
        circleCompanionEdgewiseTetrahedron z .right :=
  LoopEdgewiseSection.outerCurves_common _ _

/-- 元の解像三単体の右辺は、元の切断の右射影を初区間で読んだもの。 -/
lemma circleCompanionEdgewiseTetrahedron_right (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 2 3 (by decide)) ≫
      circleCompanionEdgewiseTetrahedron z k =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight (LoopEdgewiseSection.arrow k)).app (1 : Fin 2) ≫
          circleBKParameter ≫ (circleEvaluationCompanionCircleMap z).right := by
  rw [circleCompanionEdgewiseTetrahedron, ← EdgewiseCoordinates.rightCurve]
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}).op Δ[1] ≫
      SSet.yonedaEquiv (LoopEdgewiseSection.parameter (circleEvaluationPointedHom z)
        (circleCompanionBKEdgewiseLoopSection z) k) =
      LoopEdgewiseSection.parameter (circleEvaluationPointedHom z)
        (circleCompanionBKEdgewiseLoopSection z) k ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (circleEvaluationPointedHom z).right := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    rfl
  rw [h, LoopEdgewiseSection.parameter, Category.assoc,
    circleCompanionBKEdgewiseLoopSection_right_central]

/-- 左の三単体の右辺は、元の companion の Hom 経路そのもの。 -/
lemma circleCompanionEdgewiseTetrahedron_right_left (z : Sp.{u} _⦋0⦌) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 2 3 (by decide)) ≫
      circleCompanionEdgewiseTetrahedron z .left = circleEvaluationCompanionHomPath z := by
  rw [circleCompanionEdgewiseTetrahedron_right]
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight CospanShape.leftArrow.{u}).app (1 : Fin 2) =
      horn₂₂.ι₀₂ ≫ cospanBKWeightIso.inv.app (AsSmall.up.obj .one) := by
    rw [← CospanShape.leftPrefix_horn, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight CospanShape.leftArrow).app (1 : Fin 2) ≫ _ = _
  rw [hp, Category.assoc, circleCompanionBKParameter_leftEdge]

/-- 参照側の三単体の右辺は、元の零 Hom 頂点で定値。 -/
lemma circleCompanionEdgewiseTetrahedron_right_right (z : Sp.{u} _⦋0⦌) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 2 3 (by decide)) ≫
      circleCompanionEdgewiseTetrahedron z .right =
        SSet.const (circleEvaluationPointedHom z).basepoint := by
  rw [circleCompanionEdgewiseTetrahedron_right]
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight CospanShape.rightArrow.{u}).app (1 : Fin 2) =
      horn₂₂.ι₁₂ ≫ cospanBKWeightIso.inv.app (AsSmall.up.obj .one) := by
    rw [← CospanShape.rightPrefix_horn, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight CospanShape.rightArrow).app (1 : Fin 2) ≫ _ = _
  rw [hp, Category.assoc, circleCompanionBKParameter_rightEdge]

/-- 二つの三単体の共通初頂点。同じ中央の解像頂点から得られる Hom 頂点。 -/
def circleCompanionEdgewiseInitialVertex (z : Sp.{u} _⦋0⦌) :=
  (circleCompanionEdgewiseTetrahedron z .left).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 4))

/-- 共通解像の実際の三単体の四頂点は、共通初頂点と三つの零頂点。 -/
lemma circleCompanionEdgewiseTetrahedron_vertices (z : Sp.{u} _⦋0⦌) (k : WalkingPair)
    (i : Fin 4) :
    (circleCompanionEdgewiseTetrahedron z k).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i) = _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.vertex
        (circleCompanionEdgewiseInitialVertex z) (circleEvaluationPointedHom z).basepoint i := by
  have h1 := congrArg (fun h : (Δ[1] : SSet.{u}) ⟶
      (circleEvaluationPointedHom z).right ↦
        h.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (circleCompanionEdgewiseTetrahedron_inner z k)
  have h2 := congrArg (fun h : (Δ[1] : SSet.{u}) ⟶
      (circleEvaluationPointedHom z).right ↦
        h.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (circleCompanionEdgewiseTetrahedron_inner z k)
  simp only [NatTrans.comp_app, types_comp_apply, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edgeMap_vertex,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex, ↓reduceIte] at h1 h2
  change (circleCompanionEdgewiseTetrahedron z k).app _
    (stdSimplex.obj₀Equiv.symm (1 : Fin 4)) = (circleEvaluationPointedHom z).basepoint at h1
  change (circleCompanionEdgewiseTetrahedron z k).app _
    (stdSimplex.obj₀Equiv.symm (2 : Fin 4)) = (circleEvaluationPointedHom z).basepoint at h2
  fin_cases i
  · cases k
    · rfl
    · have h := congrArg (fun h : (Δ[1] : SSet.{u}) ⟶
          (circleEvaluationPointedHom z).right ↦
            h.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
        (circleCompanionEdgewiseTetrahedron_outer z)
      simp only [NatTrans.comp_app, types_comp_apply, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edgeMap_vertex,
        ↓reduceIte] at h
      exact h.symm
  · exact h1
  · exact h2
  · cases k
    · have h := congrArg (fun h : (Δ[1] : SSet.{u}) ⟶
          (circleEvaluationPointedHom z).right ↦
            h.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
        (circleCompanionEdgewiseTetrahedron_right_left z)
      simp only [NatTrans.comp_app, types_comp_apply, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edgeMap_vertex] at h
      exact h.trans (circleEvaluationCompanion_vertex z 1)
    · have h := congrArg (fun h : (Δ[1] : SSet.{u}) ⟶
          (circleEvaluationPointedHom z).right ↦
            h.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
        (circleCompanionEdgewiseTetrahedron_right_right z)
      simp only [NatTrans.comp_app, types_comp_apply, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edgeMap_vertex,
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
      exact h

/-- 元の共通解像三単体の同じ辺を、指定した共通初頂点と零頂点へ表示する。 -/
def circleCompanionEdgewiseFramedEdge (z : Sp.{u} _⦋0⦌) (k : WalkingPair)
    (i j : Fin 4) (hij : i ≤ j) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge (circleCompanionEdgewiseTetrahedron z k)
    (circleCompanionEdgewiseInitialVertex z) (circleEvaluationPointedHom z).basepoint
    (circleCompanionEdgewiseTetrahedron_vertices z k) i j hij

/-- フレーム付けは、元の辺の一単体を変更しない。 -/
lemma circleCompanionEdgewiseFramedEdge_simplex (z : Sp.{u} _⦋0⦌) (k : WalkingPair)
    (i j : Fin 4) (hij : i ≤ j) :
    (circleCompanionEdgewiseFramedEdge z k i j hij).edge =
      (circleCompanionEdgewiseTetrahedron z k).app (Opposite.op ⦋1⦌)
        (stdSimplex.edge 3 i j hij) := rfl

local instance companionEdgewiseTetrahedronHomKan (z : Sp.{u} _⦋0⦌) :
    KanComplex (circleEvaluationPointedHom z).right := by
  change KanComplex (mappingSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (nativeCotensorInput PointedSimplicialSet.circle z).val)
  infer_instance

local instance companionEdgewiseTetrahedronEdgeIso (z : Sp.{u} _⦋0⦌)
    {x y : (circleEvaluationPointedHom z).right _⦋0⦌}
    (e : (circleEvaluationPointedHom z).right.Edge x y) :
    IsIso (SSet.HomotopyCategory.homMk e) :=
  IsGroupoid.all_isIso (C := hoFunctor.obj (circleEvaluationPointedHom z).right) _

/-- 左三単体のフレーム付き右辺も、元の companion 経路の一単体を保つ。 -/
lemma circleCompanionEdgewiseFramedEdge_companion (z : Sp.{u} _⦋0⦌) :
    (circleCompanionEdgewiseFramedEdge z .left 2 3 (by decide)).edge =
      SSet.yonedaEquiv (circleEvaluationCompanionHomPath z) := by
  have h := congrArg SSet.yonedaEquiv (circleCompanionEdgewiseTetrahedron_right_left z)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

/-- 元の companion の解像切断の差は、同じ元の右辺の逆の類を表す。 -/
lemma circleCompanionEdgewise_difference_inverse (z : Sp.{u} _⦋0⦌) :
    inv (SSet.HomotopyCategory.homMk
        (circleCompanionEdgewiseFramedEdge z .right 0 1 (by decide))) ≫
      SSet.HomotopyCategory.homMk
        (circleCompanionEdgewiseFramedEdge z .left 0 1 (by decide)) =
    inv (SSet.HomotopyCategory.homMk
      (circleCompanionEdgewiseFramedEdge z .left 2 3 (by decide))) := by
  have hi (k : WalkingPair) := congrArg SSet.yonedaEquiv
    (circleCompanionEdgewiseTetrahedron_inner z k)
  have hr := congrArg SSet.yonedaEquiv
    (circleCompanionEdgewiseTetrahedron_right_right z)
  have ho := congrArg SSet.yonedaEquiv (circleCompanionEdgewiseTetrahedron_outer z)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hi hr ho
  have hc : SSet.yonedaEquiv
      (SSet.const (X := (Δ[1] : SSet.{u})) (circleEvaluationPointedHom z).basepoint) =
        ((circleEvaluationPointedHom z).right.σ 0) (circleEvaluationPointedHom z).basepoint := by
    have h := stdSimplex.yonedaEquiv_σ_comp
      (SSet.const (X := (Δ[0] : SSet.{u})) (circleEvaluationPointedHom z).basepoint) (0 : Fin 1)
    rw [SSet.comp_const, SSet.yonedaEquiv_const] at h
    exact h
  rw [hc] at hi hr
  have his (k : WalkingPair) :
      (circleCompanionEdgewiseTetrahedron z k).app (Opposite.op ⦋1⦌)
        (stdSimplex.edge 3 1 2 (by decide)) =
      ((circleEvaluationPointedHom z).right.σ 0) (circleEvaluationPointedHom z).basepoint := by
    exact hi k
  have hrs : (circleCompanionEdgewiseTetrahedron z .right).app (Opposite.op ⦋1⦌)
      (stdSimplex.edge 3 2 3 (by decide)) =
      ((circleEvaluationPointedHom z).right.σ 0) (circleEvaluationPointedHom z).basepoint := hr
  exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.difference_inverse _ _ _ _
    (circleCompanionEdgewiseTetrahedron_vertices z .left)
    (circleCompanionEdgewiseTetrahedron_vertices z .right) (his .left) (his .right) hrs ho

end SerrePositivity.KST.Spectra.OmegaSpectrum
