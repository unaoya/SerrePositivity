module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：底の図式を固定する相対関手単体集合と、そのパラメータ付き普遍性。
方針：内部 Hom の後合成の頂点 fiber を取り、curry と uncurry で図式の族と往復する。
規約：left fibration の場合には底の quasicategory 性なしに Kan 複体となる。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、left fibration の strict transport の関手空間。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：底の図式 a に厳密に重なる E 値の相対関手単体集合。
方針：後合成 p の内部 Hom の functorVertex a 上の fiber を取る。
規約：p と a の充填性は定義には不要。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の値の構成。 -/
@[kerodon 01AB]
def relativeFunctorSpace {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)

/-- 概要：相対関手への族を、底に重なる図式の族へ展開する。
方針：fiber の包含に続けて uncurry する。
規約：パラメータ T は直積の右因子。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手の評価と部分族の制限。 -/
def relativeFunctorUncurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (f : T ⟶ relativeFunctorSpace p a) : A ⊗ T ⟶ E :=
  uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))

/-- 概要：相対関手の族の底への合成は指定図式の定値族。
方針：fiber の固定条件を uncurry する。
規約：底のパラメータ依存は第一射影で消える。
使われ方：Kerodon §5.3.1（Tag 035D）、相対図式の可換条件。 -/
lemma relativeFunctorUncurry_projection {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (f : T ⟶ relativeFunctorSpace p a) :
    relativeFunctorUncurry f ≫ p = fst A T ≫ a := by
  unfold relativeFunctorUncurry
  rw [← uncurry_natural_right, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
    SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：底に厳密に重なる図式の族は相対関手への族を定める。
方針：curry した族を後合成の fiber へ持ち上げる。
規約：底の条件は射の等式として指定する。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手単体集合の普遍性の逆向き。 -/
def relativeFunctorCurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (H : A ⊗ T ⟶ E) (hH : H ≫ p = fst A T ≫ a) :
    T ⟶ relativeFunctorSpace p a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry H) (by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, hH, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex])

/-- 概要：相対図式の族を curry して展開すると元の図式に戻る。
方針：fiber の持ち上げと curry の往復を使う。
規約：底の固定条件の証明の選択には依存しない。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手の族の回収。 -/
lemma relativeFunctorUncurry_curry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (H : A ⊗ T ⟶ E) (hH : H ≫ p = fst A T ≫ a) :
    relativeFunctorUncurry (relativeFunctorCurry H hH) = H := by
  exact uncurry_curry H

/-- 概要：相対関手への族は展開した図式の族から一意に決まる。
方針：curry の単射性と fiber の包含後の等式判定を使う。
規約：任意のパラメータ T を許す。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手の射の等式の検査。 -/
lemma relativeFunctorUncurry_injective {A T E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    Function.Injective (relativeFunctorUncurry (T := T) (p := p) (a := a)) := by
  intro f g h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _ _ (uncurry_injective h)

/-- 概要：left fibration 上の相対関手単体集合は Kan 複体。
方針：後合成の left fibration 性と頂点 fiber の Kan 判定を使う。
規約：A、E、B の quasicategory 性は要求しない。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、strict transport の Kan 値性。 -/
@[kerodon 01GM, kerodon 01GZ]
instance relativeFunctorSpace_kanComplex {A E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (a : A ⟶ B) : KanComplex (relativeFunctorSpace p a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "A.4.17" (partial := component) "仮定：Y→Sing(X)とSing(U)→Sing(X)を指定（HAの入力に一致する単体集合模型）。結論：底上の全単体的写像空間Fun_SingX(Sing(U),Y)をinternal Homのfiberで構成する（θ(U,Y)の値の式に一致する部分）。θ全体の関手性、モデル圏のfibrant-cofibrant比較、層条件、ΨXとその全nerveの構成は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace
attribute [cite HA "A.7.3" (partial := component) "仮定：p:E→N(A)をexit-path射影の入力模型として指定し、chain aを∆n→N(A)で与える（HAの式の入力に一致）。結論：内部Homからchainの点へのfiberでFun_{N(A)}(∆n,E)を構成する（SingA(X)[a]の表示に一致）。位相空間からのE=SingA(X)自体の構成は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace
attribute [cite HA "A.7.4" (partial := stronger-hyp) "仮定：p:E→N(A)がleft fibrationである場合に限定（Leanが強い：HAのinner fibrationに代えてleft fibrationを追加）。結論：任意∆n→N(A)上のrelativeFunctorSpaceはKan complex（表示された固定chainのfiberのKan性に一致）。conicalなXからSingAを構成し一般inner fibrationの場合にも適用する比較は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex
attribute [cite HA "A.9.2" (partial := component) "仮定：p:Y→SingA(X)をleft fibration、a:SingA(U)→SingA(X)を指定（HAのfibrant入力の単体的条件に一致）。結論：底上のrelativeFunctorSpaceを定め、その値がKan complexとなる（θ(U,Y)の式とKan性に一致する部分）。位相的SingAの構成、全(U,Y)でのfunctoriality、covariant model structureとcoherent nerve、およびΨX全体の構成は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace
attribute [cite HA "A.9.2" (partial := component) "仮定：p:Y→SingA(X)をleft fibration、a:SingA(U)→SingA(X)を指定（HAのfibrant入力の単体的条件に一致）。結論：底上のrelativeFunctorSpaceを定め、その値がKan complexとなる（θ(U,Y)の式とKan性に一致する部分）。位相的SingAの構成、全(U,Y)でのfunctoriality、covariant model structureとcoherent nerve、およびΨX全体の構成は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex
