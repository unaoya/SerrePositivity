module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInternalHom
public import SerrePositivity.InfinityCategories.Core.LeftFiberKan
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：底の図式を固定する相対関手単体集合と、そのパラメータ付き普遍性。
方針：内部 Hom の後合成の頂点 fiber を取り、curry と uncurry で図式の族と往復する。
規約：left fibration の場合には底の quasicategory 性なしに Kan 複体となる。
使われ方：Kerodon Construction 5.3.1.5、left fibration の strict transport の関手空間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底の図式 a に厳密に重なる E 値の相対関手単体集合。
方針：後合成 p の内部 Hom の functorVertex a 上の fiber を取る。
規約：p と a の充填性は定義には不要。
使われ方：Kerodon §5.3.1、strict transport の値の構成。 -/
@[kerodon 01AB]
def relativeFunctorSpace {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) : SSet.{u} :=
  vertexFiber ((ihom A).map p) (functorVertex a)

/-- 概要：相対関手への族を、底に重なる図式の族へ展開する。
方針：fiber の包含に続けて uncurry する。
規約：パラメータ T は直積の右因子。
使われ方：Kerodon §5.3.1、相対関手の評価と部分族の制限。 -/
def relativeFunctorUncurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (f : T ⟶ relativeFunctorSpace p a) : A ⊗ T ⟶ E :=
  uncurry (f ≫ vertexFiberι ((ihom A).map p) (functorVertex a))

/-- 概要：相対関手の族の底への合成は指定図式の定値族。
方針：fiber の固定条件を uncurry する。
規約：底のパラメータ依存は第一射影で消える。
使われ方：Kerodon §5.3.1、相対図式の可換条件。 -/
lemma relativeFunctorUncurry_projection {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (f : T ⟶ relativeFunctorSpace p a) :
    relativeFunctorUncurry f ≫ p = fst A T ≫ a := by
  unfold relativeFunctorUncurry
  rw [← uncurry_natural_right, Category.assoc, vertexFiberι_comp,
    SSet.comp_const, uncurry_const_functorVertex]

/-- 概要：底に厳密に重なる図式の族は相対関手への族を定める。
方針：curry した族を後合成の fiber へ持ち上げる。
規約：底の条件は射の等式として指定する。
使われ方：Kerodon §5.3.1、相対関手単体集合の普遍性の逆向き。 -/
def relativeFunctorCurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (H : A ⊗ T ⟶ E) (hH : H ≫ p = fst A T ≫ a) :
    T ⟶ relativeFunctorSpace p a :=
  vertexFiberLift _ _ (curry H) (by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, hH, uncurry_const_functorVertex])

/-- 概要：相対図式の族を curry して展開すると元の図式に戻る。
方針：fiber の持ち上げと curry の往復を使う。
規約：底の固定条件の証明の選択には依存しない。
使われ方：Kerodon §5.3.1、相対関手の族の回収。 -/
lemma relativeFunctorUncurry_curry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (H : A ⊗ T ⟶ E) (hH : H ≫ p = fst A T ≫ a) :
    relativeFunctorUncurry (relativeFunctorCurry H hH) = H := by
  exact uncurry_curry H

/-- 概要：相対関手への族は展開した図式の族から一意に決まる。
方針：curry の単射性と fiber の包含後の等式判定を使う。
規約：任意のパラメータ T を許す。
使われ方：Kerodon §5.3.1、相対関手の射の等式の検査。 -/
lemma relativeFunctorUncurry_injective {A T E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    Function.Injective (relativeFunctorUncurry (T := T) (p := p) (a := a)) := by
  intro f g h
  exact vertexFiber_hom_ext _ _ (uncurry_injective h)

/-- 概要：left fibration 上の相対関手単体集合は Kan 複体。
方針：後合成の left fibration 性と頂点 fiber の Kan 判定を使う。
規約：A、E、B の quasicategory 性は要求しない。
使われ方：Kerodon Construction 5.3.1.5、strict transport の Kan 値性。 -/
@[kerodon 01GM, kerodon 01GZ]
instance relativeFunctorSpace_kanComplex {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (a : A ⟶ B) : KanComplex (relativeFunctorSpace p a) :=
  vertexFiber_kanComplex_of_leftFibration ((ihom A).map p) (functorVertex a)

end SerrePositivity.InfinityCategories
