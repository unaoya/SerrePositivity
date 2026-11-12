module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanUnstraighteningUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanQuotientRelativeDescent

/-!
概要：元の marked span 全族から、同じ商図式の小さい unstraightening への実写像。
方針：Ind-S (5) の元の単位を相対初頂点降下へ代入する。
規約：元の全族と q を厳密に保持する。全 fiber 回収と既存指定点比較は別途検証する。
使われ方：K-B-S の実全族写像本体。一般の商・局所化 API は追加しない。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：元の marked span 全族を、同じ商上の小さい unstraightening へ送る実写像。
方針：同じ Ind-S 単位と底条件を既存の相対降下構成へ渡す。
規約：全族単位や相対降下同値性の追加入力は不要。
使われ方：K-B-S の全 fiber・指定恒等点比較を行う固定写像。 -/
def weakSpanKanQuotientFamilyMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientRelativeTotalMap h x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanUnstraighteningUnit i x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanUnstraighteningUnit_projection i x)

/-- 概要：同じ実全族写像は元の底射影と q の合成を厳密に保持する。
方針：元の単位を代入した同じ相対降下の底条件を使う。
規約：底上の同型だけでは代用しない。
使われ方：元の全族の各実 fiber への制限。 -/
theorem weakSpanKanQuotientFamilyMap_projection :
    weakSpanKanQuotientFamilyMap h x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x ≫ q.hom :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientRelativeTotalMap_projection h x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanUnstraighteningUnit i x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanUnstraighteningUnit_projection i x)

/-- 概要：同じ実全族の初頂点制限は、元の単体圏単位の商像を相対空間内で回収する。
方針：代入した同じ実単位に対する相対降下の指定同型を保持する。
規約：全空間だけの絶対同型に弱めず、元の底を固定した比較を使う。
使われ方：K-B-S の元の全 fiber 単位回収への入力。 -/
def weakSpanKanQuotientFamilyMapRestrictionIso :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientRelativeTotalMapRestrictionIso h x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanUnstraighteningUnit i x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanUnstraighteningUnit_projection i x)

end SerrePositivity.KST.Fibration
