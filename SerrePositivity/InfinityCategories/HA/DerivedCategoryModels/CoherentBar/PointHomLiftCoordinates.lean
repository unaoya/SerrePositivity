module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColimitPointHomCriterion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftHomComparison
/-!
概要：標準 Hom の持ち上げを実余錐族として読み、最初と最後の制限を計算する。
方針：二重 coslice の join 単体を一点前置の標準単体へ移す。
規約：切断を選び直さず、既存の InitialTotal の全単体で計算する。
使われ方：native 恒等成分と終点の Hom 比較を結ぶ高次補正の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {E B : SSet.{u}} (p : E ⟶ B) (d : E _⦋0⦌) (y : B _⦋0⦌)

def dgCoherentBarPointLiftSimplex {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal p d y) _⦋n⦌) : E _⦋n + 1⦌ :=
  SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫ t.val.val)

lemma dgCoherentBarPointLiftSimplex_source {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal p d y) _⦋n⦌) :
    E.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (dgCoherentBarPointLiftSimplex p d y t) = d := by
  change E.map _ (SSet.yonedaEquiv _) = d
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso_first_inv,
    t.val.property, Equiv.apply_symm_apply]

lemma dgCoherentBarPointLiftSimplex_tail {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal p d y) _⦋n⦌) :
    E.δ 0 (dgCoherentBarPointLiftSimplex p d y t) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation p d y).app (Opposite.op ⦋n⦌) t).val := by
  change E.map _ (SSet.yonedaEquiv _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso_face_inv]
  rfl

lemma dgCoherentBarPointLiftSimplex_projection {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal p d y) _⦋n⦌) :
    p.app (Opposite.op ⦋n + 1⦌) (dgCoherentBarPointLiftSimplex p d y t) =
      SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫ (t.val.val ≫ p)) := by
  simpa only [dgCoherentBarPointLiftSimplex, Category.assoc] using
    (SSet.yonedaEquiv_comp ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫ t.val.val) p).symm

lemma dgCoherentBarPointLiftSimplex_map {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal p d y) _⦋n⦌) :
    E.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom)).op
      (dgCoherentBarPointLiftSimplex p d y t) =
        dgCoherentBarPointLiftSimplex p d y
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal p d y).map α.op t) := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso.{u} n).inv =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso m).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.stdSimplex.map α) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality α]
    erw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change E.map _ (SSet.yonedaEquiv _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, hi]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
