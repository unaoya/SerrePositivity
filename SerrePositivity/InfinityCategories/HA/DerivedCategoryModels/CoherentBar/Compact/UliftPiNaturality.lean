module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiComparison
/-!
概要：全基点 π の宇宙比較は、元の実単体的射と可換する。
方針：標準単体の宇宙同型で球面代表の自然性を計算し、商へ渡す。
規約：基点とその像を明示し、群同型の選択を変えない。
使われ方：native 評価の実脚のチャートを追加宇宙から戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {X Y : SSet.{u}}

lemma dgBarCompactPointedSimplexUp_naturality (φ : X ⟶ Y) {n : ℕ} {x : X _⦋0⦌}
    (f : X.PtSimplex n x) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ rfl f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (x := ULift.up x) (y := ULift.up (φ.app _ x))
        ((SSet.uliftFunctor.{v, u}).map φ) rfl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp.{u, v} f) := by
  apply RelativeMorphism.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map (f.map ≫ φ) =
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f.map) ≫
      (SSet.uliftFunctor.{v, u}).map φ
  rw [Functor.map_comp, Category.assoc]

lemma dgBarCompactUliftPiEquiv_naturality [KanComplex X] [KanComplex Y]
    (φ : X ⟶ Y) (n : ℕ) (x : X _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{u, v} Y n (φ.app _ x) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ rfl a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (x := ULift.up x) (y := ULift.up (φ.app _ x))
        ((SSet.uliftFunctor.{v, u}).map φ) rfl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{u, v} X n x a) := by
  induction a using Quotient.inductionOn with | h f => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ rfl f)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (x := ULift.up x) (y := ULift.up (φ.app _ x))
      ((SSet.uliftFunctor.{v, u}).map φ) rfl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp.{u, v} f))
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (dgBarCompactPointedSimplexUp_naturality φ f)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
