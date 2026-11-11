module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionConeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.FixedApexLimitCriterion

/-!
概要：固定頂点の coslice の切断の族と、右因子にパラメータを持つ join の図式の普遍性。
方針：相対関手空間の普遍性と coslice の curry と uncurry を合成する。
規約：左端は x の一点、右端はパラメータを忘れた元の図式 p に固定する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断側の模型の比較の準備。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：固定頂点の切断の族を、右因子にパラメータを持つ join 上の図式へ展開する。
方針：相対関手の評価を coslice から uncurry する。
規約：パラメータ A は K との直積の右因子。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の相対 join 延長に入力する図式。 -/
noncomputable def sectionConeUncurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry f)

/-- 概要：展開した切断の族の左端は指定頂点の一点の射。
方針：coslice の uncurry の固定条件を使う。
規約：全次数で頂点を固定する。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の左端を保つ join 図式の構成。 -/
lemma sectionConeUncurry_inl {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (K ⊗ A) ≫ sectionConeUncurry f = SSet.yonedaEquiv.symm x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed _

/-- 概要：展開した切断の族の右端は元の図式の定値族。
方針：coslice の射影と相対関手の評価の固定条件を使う。
規約：第一射影でパラメータ A を忘れる。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の右端を保つ join 図式の構成。 -/
lemma sectionConeUncurry_inr {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (K ⊗ A) ≫ sectionConeUncurry f = fst K A ≫ p := by
  rw [sectionConeUncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection]

/-- 概要：切断の族の展開はパラメータの前合成と可換。
方針：相対評価の自然性と coslice の uncurry の自然性を使う。
規約：底の図式と頂点は共通に固定する。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の部分族を保つ相対 join 延長の準備。 -/
lemma sectionConeUncurry_precomp {A B K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) (a : A ⟶ B) :
    sectionConeUncurry (a ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (K ◁ a) ≫ sectionConeUncurry f := by
  unfold sectionConeUncurry
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp]

/-- 概要：切断の族は join 上へ展開した図式で決まる。
方針：coslice と相対関手の二つの uncurry の単射性を順に使う。
規約：充填性の仮定は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の切断模型の射の等式の検査。 -/
lemma sectionConeUncurry_injective {A K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    Function.Injective (sectionConeUncurry (A := A) (p := p) (x := x)) := by
  intro f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (SSet.yonedaEquiv.symm x) h

/-- 概要：左端と右図式を固定した join の図式を切断の族へ戻す。
方針：coslice へ curry し、射影の固定条件で相対関手空間へ curry する。
規約：パラメータは右図式の直積の右因子。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の join 延長からの逆射の構成。 -/
noncomputable def sectionConeCurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (K ⊗ A) ≫ F = SSet.yonedaEquiv.symm x)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (K ⊗ A) ≫ F = fst K A ≫ p) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F hx) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection]; exact hp)

/-- 概要：join の図式を切断の族へ curry して展開すると元に戻る。
方針：相対関手と coslice の二つの往復則を使う。
規約：固定条件の証明の選択には依存しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の切断模型の普遍性の一方の逆則。 -/
lemma sectionConeUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (K ⊗ A) ≫ F = SSet.yonedaEquiv.symm x)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (K ⊗ A) ≫ F = fst K A ≫ p) :
    sectionConeUncurry (sectionConeCurry F hx hp) = F := by
  rw [sectionConeUncurry, sectionConeCurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]

/-- 概要：切断の族を展開して curry すると元の族になる。
方針：展開の単射性と図式側の往復則を使う。
規約：A・K・X の充填性を要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の切断模型の普遍性の他方の逆則。 -/
lemma sectionConeCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) :
    sectionConeCurry (sectionConeUncurry f) (sectionConeUncurry_inl f)
      (sectionConeUncurry_inr f) = f := by
  apply sectionConeUncurry_injective p x
  rw [sectionConeUncurry_curry]

/-- 概要：切断の族と両端を固定した右パラメータ付き join 図式は全単射で対応する。
方針：二つの curry と uncurry の普遍性と往復則をまとめる。
規約：任意パラメータについての普遍性を与える。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断側の標準比較の検証。 -/
noncomputable def sectionConeHomEquiv {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) ≃
      {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X //
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (K ⊗ A) ≫ F = SSet.yonedaEquiv.symm x ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (K ⊗ A) ≫ F = fst K A ≫ p} where
  toFun f := ⟨sectionConeUncurry f, sectionConeUncurry_inl f, sectionConeUncurry_inr f⟩
  invFun F := sectionConeCurry F.val F.property.1 F.property.2
  left_inv f := sectionConeCurry_uncurry f
  right_inv F := Subtype.ext (sectionConeUncurry_curry F.val F.property.1 F.property.2)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
