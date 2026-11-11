module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSubdivision
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinSimplexShapes

/-!
概要：元の edgewise 重みの宇宙変更を、同じ大きい宇宙の重みへ厳密に比較する。
方針：標準単体の反転・join・宇宙の同型を合成し、全単調写像に関する自然性を示す。
規約：全重みと全単体作用を保持し、次数ごとの任意の同型で代用しない。
使われ方：twisted arrow の全射影と共同 Hom 図式の宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 反転した標準単体の宇宙持ち上げを、同じ大きい反転標準単体へ比較する。 -/
def uliftOppositeStdSimplexIso (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (Δ[n] : SSet.{u}).op ≅ (Δ[n] : SSet.{max u v}).op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso Δ[n] ≪≫ SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n)

/-- 元の反転標準単体の宇宙比較は、元の全単調写像を保つ。 -/
lemma uliftOppositeStdSimplexIso_hom_map {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).map (SSet.opFunctor.map (stdSimplex.map α)) ≫
      (uliftOppositeStdSimplexIso n).hom =
    (uliftOppositeStdSimplexIso m).hom ≫
      SSet.opFunctor.map (stdSimplex.map α : (Δ[m] : SSet.{max u v}) ⟶ Δ[n]) := by
  apply SSet.hom_ext
  intro k
  rfl

/-- 元の edgewise 重みの宇宙持ち上げと、同じ大きい宇宙の重みの厳密な同型。 -/
def edgewiseWeightUniverseIso (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.obj ⦋n⦌) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{max u v}.obj ⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso (Δ[n] : SSet.{u}).op Δ[n] ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (uliftOppositeStdSimplexIso n) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso n)

/-- 元の重みの宇宙比較は、元の全単調写像に対して自然。 -/
lemma edgewiseWeightUniverseIso_hom_map {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map α) ≫
      (edgewiseWeightUniverseIso.{u, v} n).hom =
    (edgewiseWeightUniverseIso.{u, v} m).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{max u v}.map α := by
  dsimp only [edgewiseWeightUniverseIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_hom_naturality]
  simp only [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  rw [uliftOppositeStdSimplexIso_hom_map, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso_hom_map]

/-- 元の重みの宇宙比較の逆も、元の全単調写像を保つ。 -/
lemma edgewiseWeightUniverseIso_inv_map {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{max u v}.map α ≫ (edgewiseWeightUniverseIso.{u, v} n).inv =
      (edgewiseWeightUniverseIso.{u, v} m).inv ≫
        (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map α) := by
  apply (cancel_epi (edgewiseWeightUniverseIso.{u, v} m).hom).mp
  rw [← Category.assoc, ← edgewiseWeightUniverseIso_hom_map.{u, v}, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
