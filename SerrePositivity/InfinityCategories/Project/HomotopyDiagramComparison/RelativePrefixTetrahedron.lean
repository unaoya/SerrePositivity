module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightAnodyneJoinPrefix

/-!
概要：指定された三角形に辺を前置し、底の指定四面体を保つ実際の四面体へ延長する。
方針：辺と区間の join を使い、終点への相対 coslice 制限の自明 Kan fibration 性を適用する。
規約：元の三角形・前置辺・底の三単体を全て厳密に保持する。
使われ方：共通部分の始対象の比較辺と、指定右修正三角形を一つの高次整合性へ束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 点と辺の join の最初の頂点を面写像で表示する。 -/
lemma joinPointEdge_firstVertex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl]
  apply SSet.yonedaEquiv.injective
  decide

/-- 二つの辺の join の最初の辺を面写像で表示する。 -/
lemma joinEdgeEdge_firstEdge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 1).hom =
      stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl]
  apply SSet.yonedaEquiv.injective
  decide

/-- 指定三角形に指定辺を前置し、指定した底の四面体を覆う三単体が存在する。 -/
lemma exists_prefixTetrahedron_over_innerFibration {E B : SSet.{u}}
    (q : E ⟶ B) [InnerFibration q]
    (a : (Δ[1] : SSet.{u}) ⟶ E) (t : (Δ[2] : SSet.{u}) ⟶ E)
    (ha : (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫ t =
      stdSimplex.δ (0 : Fin 2) ≫ a)
    (v : (Δ[3] : SSet.{u}) ⟶ B)
    (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫ v = a ≫ q)
    (ht : stdSimplex.δ (0 : Fin 4) ≫ v = t ≫ q) :
    ∃ s : (Δ[3] : SSet.{u}) ⟶ E,
      (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫ s = a ∧
      stdSimplex.δ (0 : Fin 4) ≫ s = t ∧ s ≫ q = v := by
  let A := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ t
  let V := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 1).hom ≫ v
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ A = stdSimplex.δ (0 : Fin 2) ≫ a := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ t) joinPointEdge_firstVertex).trans ha)
  have hV : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[1] ≫ V = a ≫ q := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ v) joinEdgeEdge_firstEdge).trans he)
  let aa := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry A hA
  let bb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry V hV
  have hab : aa ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ a) q =
      bb ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (a ≫ q) (stdSimplex.δ (0 : Fin 2)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    dsimp only [A, V]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEdgeEdge_terminalFace]
    simp only [Category.assoc, ht]
  obtain ⟨L, hL, hq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.exists_relativeEdgeCosliceLift a q aa bb hab
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry L
  have hJ : stdSimplex.δ (0 : Fin 4) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 1).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 Δ[1]) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 1).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEdgeEdge_terminalFace, Iso.inv_hom_id_assoc]
  refine ⟨s, ?_, ?_, ?_⟩
  · have hJ₀ : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 1).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[1] Δ[1] := by
      rw [← joinEdgeEdge_firstEdge, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    dsimp only [s]
    rw [← Category.assoc, hJ₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]
  · dsimp only [s]
    rw [← Category.assoc, hJ, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, hL,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    dsimp only [A]
    rw [Iso.inv_hom_id_assoc]
  · dsimp only [s]
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, hq, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    dsimp only [V]
    rw [Iso.inv_hom_id_assoc]

/-- 右退化した三角形の先頭辺は、元の三角形の先頭辺。 -/
lemma degenerateTetrahedron_firstEdge :
    ((stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
      stdSimplex.σ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 右退化した三角形の終端面は、後半の辺の右退化。 -/
lemma degenerateTetrahedron_terminalFace :
    (stdSimplex.δ (0 : Fin 4) ≫ stdSimplex.σ (2 : Fin 3) : (Δ[2] : SSet.{u}) ⟶ Δ[2]) =
      stdSimplex.σ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 底が元の三角形の右退化である場合の、前置辺と終端三角形を保持する四面体。 -/
lemma exists_prefixTetrahedron_over_degenerateTriangle {E B : SSet.{u}}
    (q : E ⟶ B) [InnerFibration q]
    (a : (Δ[1] : SSet.{u}) ⟶ E) (t : (Δ[2] : SSet.{u}) ⟶ E)
    (ha : (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫ t =
      stdSimplex.δ (0 : Fin 2) ≫ a)
    (v : (Δ[2] : SSet.{u}) ⟶ B)
    (he : stdSimplex.δ (2 : Fin 3) ≫ v = a ≫ q)
    (ht : t ≫ q = stdSimplex.σ (1 : Fin 2) ≫ (stdSimplex.δ (0 : Fin 3) ≫ v)) :
    ∃ s : (Δ[3] : SSet.{u}) ⟶ E,
      (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫ s = a ∧
      stdSimplex.δ (0 : Fin 4) ≫ s = t ∧
      s ≫ q = stdSimplex.σ (2 : Fin 3) ≫ v := by
  apply exists_prefixTetrahedron_over_innerFibration q a t ha
    (stdSimplex.σ (2 : Fin 3) ≫ v)
  · rw [← Category.assoc, degenerateTetrahedron_firstEdge, he]
  · rw [← Category.assoc, degenerateTetrahedron_terminalFace, Category.assoc, ht]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
