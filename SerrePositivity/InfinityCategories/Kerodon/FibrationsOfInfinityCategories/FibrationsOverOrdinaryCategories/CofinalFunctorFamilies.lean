module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalProductTest

/-!
概要：相対関手空間へのパラメータ付きの族と底上の図式の族の対応。
方針：頂点 fiber の包含を curry と uncurry で往復する。
規約：F1 の同じ一般構成を narrow import の cofinalFunctorSpace に対して証明する。
使われ方：Kerodon §5.3.1（Tag 035D）、cofinality の底図式の引き戻しと合成。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：相対関手への族を、底に重なる図式の族へ展開する。
方針：fiber の包含に続けて uncurry する。
規約：パラメータ T は直積の右因子。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手の評価と部分族の制限。 -/
def cofinalFunctorUncurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p a) : A ⊗ T ⟶ E :=
  uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))

/-- 概要：相対関手の族の底への合成は指定図式の定値族。
方針：fiber の固定条件を uncurry する。
規約：底のパラメータ依存は第一射影で消える。
使われ方：Kerodon §5.3.1（Tag 035D）、相対図式の可換条件。 -/
lemma cofinalFunctorUncurry_projection {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p a) :
    cofinalFunctorUncurry f ≫ p = fst A T ≫ a := by
  unfold cofinalFunctorUncurry
  rw [← uncurry_natural_right, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
    SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalUncurry_const_functorVertex]

/-- 概要：底に厳密に重なる図式の族は相対関手への族を定める。
方針：curry した族を後合成の fiber へ持ち上げる。
規約：底の条件は射の等式として指定する。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手単体集合の普遍性の逆向き。 -/
def cofinalFunctorCurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (H : A ⊗ T ⟶ E) (hH : H ≫ p = fst A T ≫ a) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry H) (by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, hH, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalUncurry_const_functorVertex])

/-- 概要：相対図式の族を curry して展開すると元の図式に戻る。
方針：fiber の持ち上げと curry の往復を使う。
規約：底の固定条件の証明の選択には依存しない。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手の族の回収。 -/
lemma cofinalFunctorUncurry_curry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (H : A ⊗ T ⟶ E) (hH : H ≫ p = fst A T ≫ a) :
    cofinalFunctorUncurry (cofinalFunctorCurry H hH) = H := by
  exact uncurry_curry H

/-- 概要：相対関手への族は展開した図式の族から一意に決まる。
方針：curry の単射性と fiber の包含後の等式判定を使う。
規約：任意のパラメータ T を許す。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手の射の等式の検査。 -/
lemma cofinalFunctorUncurry_injective {A T E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    Function.Injective (cofinalFunctorUncurry (T := T) (p := p) (a := a)) := by
  intro f g h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _ _ (uncurry_injective h)

/-- 概要：相対 uncurry は底図式の始域の制限と可換。
方針：fiber の包含後の制限を通常の pre に戻し、uncurry の自然性を使う。
規約：パラメータ T も底図式 a も任意。
使われ方：底変換の同型と制限の可換性。 -/
lemma cofinalFunctorPre_uncurry {A D T E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p a) :
    cofinalFunctorUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre p a i) =
      (i ▷ T) ≫ cofinalFunctorUncurry f := by
  unfold cofinalFunctorUncurry
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre_ι, ← Category.assoc, uncurry_pre_app]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
