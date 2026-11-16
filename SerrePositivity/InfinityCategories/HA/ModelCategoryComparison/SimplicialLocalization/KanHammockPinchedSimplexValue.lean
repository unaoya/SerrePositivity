module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomPinchedValue

/-!
概要：元のKan hammockのpinched比較の同じ全単体の値に名前を付ける。
方針：既存のcoherent単体を一般の相対圏で定義し、元の評価式をそのまま記録する。
規約：elaborationの分割のみ。元のHom単体・局所化頂点・値を変更しない。
使われ方：複雑なBEの係数への特殊化でも同じ全単体の式を検査する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open scoped _root_.Simplicial
variable (C : RelativeCategory.{u}) (X Y : C.category)

/-- 元のKan hammockのHom単体を、同じ元のcoherent単体として評価する。 -/
def kanHammockPinchedSimplexValue {n : ℕ}
    (s : (exInfinity.obj (colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve C) _⦋n + 1⦌ :=
  coherentHomComparisonSimplex (show (SimplicialCategory.sHom
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y)) _⦋n⦌ from s)

/-- 元のpinched比較の同じ全単体の評価式を、名前付きの同じ値で表示する。 -/
theorem kanHammockHomPinchedMap_value {n : ℕ}
    (s : (exInfinity.obj (colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap C X Y).app (Opposite.op ⦋n⦌) s).val =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockPinchedSimplexValue C X Y s :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap_app_val C X Y s

/-- 任意のパラメータの全単体で、同じpinched比較が同じ元のcoherent値を持つという式。 -/
def KanHammockPinchedValueFormula {T : SSet.{u}}
    (f : T ⟶ exInfinity.obj (colimitGraph C.weakEquivalences X Y)) : Prop :=
  ∀ {n : ℕ} (s : T _⦋n⦌),
    (((f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap C X Y).app (Opposite.op ⦋n⦌)) s).val =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockPinchedSimplexValue C X Y (f.app (Opposite.op ⦋n⦌) s)

/-- 元の全単体の値の式を任意のパラメータ写像へ前合成する。 -/
theorem kanHammockHomPinchedMap_value_family {T : SSet.{u}}
    (f : T ⟶ exInfinity.obj (colimitGraph C.weakEquivalences X Y)) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockPinchedValueFormula C X Y f := by
  intro n s
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap_value C X Y (f.app (Opposite.op ⦋n⦌) s)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
