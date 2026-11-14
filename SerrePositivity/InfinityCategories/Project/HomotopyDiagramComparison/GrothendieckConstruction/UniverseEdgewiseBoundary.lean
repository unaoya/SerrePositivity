module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.UniverseEdgewiseWeight
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints

/-!
概要：元の edgewise 重みの宇宙同型は、始点と終点を記録する元の両包含を保つ。
方針：join の両包含と反転標準単体の宇宙比較を使い、逆同型の式も回収する。
規約：両端の全標準単体への制限を厳密に保持する。
使われ方：twisted arrow の元の全射影の宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の右包含は、同じ重みの宇宙比較と厳密に可換。 -/
lemma edgewiseWeightUniverseIso_inr (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n]) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso.{u, v} n).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{max u v}).op Δ[n] := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]

/-- 元の重みの宇宙比較の逆も、同じ右包含を保つ。 -/
lemma edgewiseWeightUniverseIso_inv_inr (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{max u v}).op Δ[n] ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso.{u, v} n).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).inv ≫
        (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n]) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso.{u, v} n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    edgewiseWeightUniverseIso_inr, Iso.inv_hom_id_assoc]

/-- 元の左包含も、同じ重みの宇宙比較と厳密に可換。 -/
lemma edgewiseWeightUniverseIso_inl (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n]) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso.{u, v} n).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftOppositeStdSimplexIso n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{max u v}).op Δ[n] := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]

/-- 元の標準単体の順序反転は、元の宇宙比較で同じ順序反転へ送られる。 -/
lemma uliftOppositeStdSimplexIso_opInv (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (stdSimplex.opIso.{u} ⦋n⦌).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftOppositeStdSimplexIso n).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).hom ≫ (stdSimplex.opIso.{max u v} ⦋n⦌).inv := by
  apply SSet.hom_ext
  intro m
  rfl

/-- 元の始点を取る全射は、同じ重みの宇宙比較と厳密に可換。 -/
lemma edgewiseWeightUniverseIso_leftEndpoint (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map
        ((stdSimplex.opIso.{u} ⦋n⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n]) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso.{u, v} n).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).hom ≫ (stdSimplex.opIso.{max u v} ⦋n⦌).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{max u v}).op Δ[n] := by
  rw [Functor.map_comp, Category.assoc, edgewiseWeightUniverseIso_inl, ← Category.assoc,
    uliftOppositeStdSimplexIso_opInv, Category.assoc]

/-- 元の始点を取る全射は、同じ重みの逆宇宙比較でも保たれる。 -/
lemma edgewiseWeightUniverseIso_inv_leftEndpoint (n : ℕ) :
    (stdSimplex.opIso.{max u v} ⦋n⦌).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{max u v}).op Δ[n] ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso.{u, v} n).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n).inv ≫ (SSet.uliftFunctor.{v, u}).map
        ((stdSimplex.opIso.{u} ⦋n⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n]) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgewiseWeightUniverseIso.{u, v} n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [edgewiseWeightUniverseIso_leftEndpoint, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
