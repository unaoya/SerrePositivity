module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion

/-!
概要：右 Kan の標準局所極限条件を定値パラメータ族へ移す。
方針：定値関手を各頂点で評価すると元に戻ることを用い、点ごとの極限判定を適用する。
規約：パラメータには quasicategory 性を要求しない。
使われ方：右 Kan 関手へ入る写像空間の元の制限の全パラメータ判定。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：定値パラメータ族への写像を一つの頂点で評価すると恒等射。
方針：内部 Hom の評価と定値関手の一次式を各次数で計算する。
規約：任意の単体集合を扱う。
使われ方：定値族の極限錐の点ごとの判定。 -/
lemma kanConstantFunctorMap_evaluate {A D : SSet.{u}} (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a = 𝟙 D := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change D.map (𝟙 n) x = x
  exact CategoryTheory.Functor.map_id_apply D n x

/-- 概要：図式と錐の値が等しければ極限性は同値。
方針：図式の等式を消去し、錐の部分型の外延性を使う。
規約：異なる表示の図式上の錐も比較する。
使われ方：標準右 Kan 錐の後合成の表示を揃える。 -/
lemma kanIsLimitCone_congr {J D : SSet.{u}} {p q : J ⟶ D} (hpq : p = q)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (hcd : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := by
  subst q
  have he : c = d := Subtype.ext hcd
  rw [he]

/-- 概要：定値パラメータ族への後合成は極限錐を保つ。
方針：各頂点での評価は元の錐なので関手圏の点ごとの極限判定を適用する。
規約：パラメータ A と添字 J は任意。
使われ方：右 Kan の局所極限を全パラメータへ移す。 -/
lemma kanIsLimitCone_constantFamily {A J D : SSet.{u}} [Quasicategory D]
    {p : J ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise
  intro a
  exact (kanIsLimitCone_congr
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram, Category.assoc,
      kanConstantFunctorMap_evaluate, Category.comp_id])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) c) a) c
    (by change (c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a = c.val
        rw [Category.assoc, kanConstantFunctorMap_evaluate, Category.comp_id])).2 hc

/-- 概要：標準右 Kan 錐の極限性は定値パラメータ族への後合成で保たれる。
方針：局所錐を定値族へ写し、標準錐との値の一致で比較する。
規約：δ とパラメータ A は任意。
使われ方：右 Kan 制限の写像空間の全パラメータ判定。 -/
lemma kanRightCanonicalLimits_constantFamily {A K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c)) :
    ∀ c : C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) c) := by
  intro c
  have hc := kanIsLimitCone_constantFamily (A := A) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c) (hF c)
  exact (kanIsLimitCone_congr
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram, Category.assoc])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D) c)
    (Category.assoc _ _ _)).1 hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
