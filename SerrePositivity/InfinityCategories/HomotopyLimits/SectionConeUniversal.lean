module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionConeFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedApexLimitCriterion

/-!
概要：固定頂点の coslice の切断の族と、右因子にパラメータを持つ join の図式の普遍性。
方針：相対関手空間の普遍性と coslice の curry と uncurry を合成する。
規約：左端は x の一点、右端はパラメータを忘れた元の図式 p に固定する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の切断側の模型の比較の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：固定頂点の切断の族を、右因子にパラメータを持つ join 上の図式へ展開する。
方針：相対関手の評価を coslice から uncurry する。
規約：パラメータ A は K との直積の右因子。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の相対 join 延長に入力する図式。 -/
noncomputable def sectionConeUncurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ coherentConeSectionSpace p x) : join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X :=
  sliceUnderUncurry (relativeFunctorUncurry f)

/-- 概要：展開した切断の族の左端は指定頂点の一点の射。
方針：coslice の uncurry の固定条件を使う。
規約：全次数で頂点を固定する。
使われ方：Kerodon 7.4.1.6 の左端を保つ join 図式の構成。 -/
lemma sectionConeUncurry_inl {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ coherentConeSectionSpace p x) :
    joinInl (Δ[0] : SSet.{u}) (K ⊗ A) ≫ sectionConeUncurry f = SSet.yonedaEquiv.symm x :=
  sliceUnderUncurry_fixed _

/-- 概要：展開した切断の族の右端は元の図式の定値族。
方針：coslice の射影と相対関手の評価の固定条件を使う。
規約：第一射影でパラメータ A を忘れる。
使われ方：Kerodon 7.4.1.6 の右端を保つ join 図式の構成。 -/
lemma sectionConeUncurry_inr {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ coherentConeSectionSpace p x) :
    joinInr (Δ[0] : SSet.{u}) (K ⊗ A) ≫ sectionConeUncurry f = fst K A ≫ p := by
  rw [sectionConeUncurry, sliceUnderUncurry_projection, relativeFunctorUncurry_projection]

/-- 概要：切断の族の展開はパラメータの前合成と可換。
方針：相対評価の自然性と coslice の uncurry の自然性を使う。
規約：底の図式と頂点は共通に固定する。
使われ方：Kerodon 7.4.1.6 の部分族を保つ相対 join 延長の準備。 -/
lemma sectionConeUncurry_precomp {A B K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : B ⟶ coherentConeSectionSpace p x) (a : A ⟶ B) :
    sectionConeUncurry (a ≫ f) =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (K ◁ a) ≫ sectionConeUncurry f := by
  unfold sectionConeUncurry
  rw [relativeFunctorUncurry_parameter, sliceUnderUncurry_precomp]

/-- 概要：切断の族は join 上へ展開した図式で決まる。
方針：coslice と相対関手の二つの uncurry の単射性を順に使う。
規約：充填性の仮定は不要。
使われ方：Kerodon 7.4.1.6 の切断模型の射の等式の検査。 -/
lemma sectionConeUncurry_injective {A K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    Function.Injective (sectionConeUncurry (A := A) (p := p) (x := x)) := by
  intro f g h
  apply relativeFunctorUncurry_injective (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p
  exact sliceUnderUncurry_injective (SSet.yonedaEquiv.symm x) h

/-- 概要：左端と右図式を固定した join の図式を切断の族へ戻す。
方針：coslice へ curry し、射影の固定条件で相対関手空間へ curry する。
規約：パラメータは右図式の直積の右因子。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の join 延長からの逆射の構成。 -/
noncomputable def sectionConeCurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (F : join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X)
    (hx : joinInl Δ[0] (K ⊗ A) ≫ F = SSet.yonedaEquiv.symm x)
    (hp : joinInr Δ[0] (K ⊗ A) ≫ F = fst K A ≫ p) : A ⟶ coherentConeSectionSpace p x :=
  relativeFunctorCurry (sliceUnderCurry F hx) (by rw [sliceUnderCurry_projection]; exact hp)

/-- 概要：join の図式を切断の族へ curry して展開すると元に戻る。
方針：相対関手と coslice の二つの往復則を使う。
規約：固定条件の証明の選択には依存しない。
使われ方：Kerodon 7.4.1.6 の切断模型の普遍性の一方の逆則。 -/
lemma sectionConeUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (F : join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X)
    (hx : joinInl Δ[0] (K ⊗ A) ≫ F = SSet.yonedaEquiv.symm x)
    (hp : joinInr Δ[0] (K ⊗ A) ≫ F = fst K A ≫ p) :
    sectionConeUncurry (sectionConeCurry F hx hp) = F := by
  rw [sectionConeUncurry, sectionConeCurry, relativeFunctorUncurry_curry,
    sliceUnderUncurry_curry]

/-- 概要：切断の族を展開して curry すると元の族になる。
方針：展開の単射性と図式側の往復則を使う。
規約：A・K・X の充填性を要求しない。
使われ方：Kerodon 7.4.1.6 の切断模型の普遍性の他方の逆則。 -/
lemma sectionConeCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ coherentConeSectionSpace p x) :
    sectionConeCurry (sectionConeUncurry f) (sectionConeUncurry_inl f)
      (sectionConeUncurry_inr f) = f := by
  apply sectionConeUncurry_injective p x
  rw [sectionConeUncurry_curry]

/-- 概要：切断の族と両端を固定した右パラメータ付き join 図式は全単射で対応する。
方針：二つの curry と uncurry の普遍性と往復則をまとめる。
規約：任意パラメータについての普遍性を与える。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の切断側の標準比較の検証。 -/
noncomputable def sectionConeHomEquiv {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) (A : SSet.{u}) :
    (A ⟶ coherentConeSectionSpace p x) ≃
      {F : join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X //
        joinInl Δ[0] (K ⊗ A) ≫ F = SSet.yonedaEquiv.symm x ∧
          joinInr Δ[0] (K ⊗ A) ≫ F = fst K A ≫ p} where
  toFun f := ⟨sectionConeUncurry f, sectionConeUncurry_inl f, sectionConeUncurry_inr f⟩
  invFun F := sectionConeCurry F.val F.property.1 F.property.2
  left_inv f := sectionConeCurry_uncurry f
  right_inv F := Subtype.ext (sectionConeUncurry_curry F.val F.property.1 F.property.2)

end SerrePositivity.InfinityCategories.HomotopyLimits
