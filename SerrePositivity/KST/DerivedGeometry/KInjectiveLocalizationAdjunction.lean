module

public import SerrePositivity.KST.DerivedGeometry.UnboundedKInjectiveModel
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：非有界ホモトピー圏から導来圏への局所化の K-injective な右随伴。
方針：構成した K-injective 模型の同値の逆と、右直交対象への Hom 全単射を使う。
規約：局所化と K-injective 分解の存在を追加の仮定にしない。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.12.6 の非有界右導来関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits DerivedCategory
namespace SerrePositivity.KST.DerivedGeometry
variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{v} C]

/--
概要：導来対象に対応する K-injective ホモトピー対象。
方針：証明済みの同値の逆を使う。
規約：関手の対象部分を指定する。
使われ方：TT §3、Toën §3.2 の局所化の右随伴。
-/
def kInjectiveLocalizationObject (Y : DerivedCategory C) : HomotopyCategory C (.up ℤ) :=
  ((kInjectiveDerivedFunctor C).asEquivalence.inverse.obj Y).obj

/--
概要：選んだ K-injective 対象の局所化と元の導来対象の標準同型。
方針：証明済みの同値の余単位を使う。
規約：実際の局所化 Qh を始域に持つ。
使われ方：TT §3、Toën §3.2 の非有界導来模型の比較。
-/
def kInjectiveLocalizationObjectIso (Y : DerivedCategory C) :
    DerivedCategory.Qh.obj (kInjectiveLocalizationObject C Y) ≅ Y :=
  (kInjectiveDerivedFunctor C).asEquivalence.counitIso.app Y

/--
概要：選んだ K-injective 対象は非輪状部分圏に右直交する。
方針：充満部分圏の対象の所属証明を用いる。
規約：同値の逆が実際に返す対象についての主張。
使われ方：TT §3、Toën §3.2 の Hom 比較。
-/
lemma kInjectiveLocalizationObject_rightOrthogonal (Y : DerivedCategory C) :
    (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal (kInjectiveLocalizationObject C Y) :=
  ((kInjectiveDerivedFunctor C).asEquivalence.inverse.obj Y).property

/--
概要：局所化された Hom と選んだ K-injective 対象へのホモトピー Hom の同値。
方針：標準同型で終域を移し、右直交対象への局所化の全単射を逆に使う。
規約：自然性を後で証明して右随伴を構成する。
使われ方：TT §3、Toën §3.2 の右導来関手の普遍性。
-/
def kInjectiveLocalizationHomEquiv (X : HomotopyCategory C (.up ℤ)) (Y : DerivedCategory C) :
    (DerivedCategory.Qh.obj X ⟶ Y) ≃ (X ⟶ kInjectiveLocalizationObject C Y) :=
  (Iso.homCongr (Iso.refl _) (kInjectiveLocalizationObjectIso C Y).symm).trans
    (Equiv.ofBijective DerivedCategory.Qh.map
      ((kInjectiveLocalizationObject_rightOrthogonal C Y).map_bijective_of_isTriangulated
        DerivedCategory.Qh X)).symm

/--
概要：Hom 比較を局所化すると、標準同型の逆との合成になる。
方針：全単射の逆の合成公式を使う。
規約：局所化の射の実際の等式。
使われ方：TT §3、Toën §3.2 の自然性の検証。
-/
lemma Qh_map_kInjectiveLocalizationHomEquiv (X : HomotopyCategory C (.up ℤ))
    (Y : DerivedCategory C) (f : DerivedCategory.Qh.obj X ⟶ Y) :
    DerivedCategory.Qh.map (kInjectiveLocalizationHomEquiv C X Y f) =
      f ≫ (kInjectiveLocalizationObjectIso C Y).inv := by
  let E := Equiv.ofBijective DerivedCategory.Qh.map
    ((kInjectiveLocalizationObject_rightOrthogonal C Y).map_bijective_of_isTriangulated
      DerivedCategory.Qh X)
  have h := E.apply_symm_apply (f ≫ (kInjectiveLocalizationObjectIso C Y).inv)
  change DerivedCategory.Qh.map (E.symm (f ≫ (kInjectiveLocalizationObjectIso C Y).inv)) = _ at h
  simpa only [kInjectiveLocalizationHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Iso.symm_hom, Category.id_comp] using h

/--
概要：Hom 比較は始域で自然。
方針：局所化の Hom 単射性を使い、局所化後の合成等式を検証する。
規約：任意のホモトピー類の射。
使われ方：TT §3、Toën §3.2 の右随伴の構成。
-/
lemma kInjectiveLocalizationHomEquiv_naturality
    (X' X : HomotopyCategory C (.up ℤ)) (Y : DerivedCategory C)
    (f : X' ⟶ X) (g : DerivedCategory.Qh.obj X ⟶ Y) :
    kInjectiveLocalizationHomEquiv C X' Y (DerivedCategory.Qh.map f ≫ g) =
      f ≫ kInjectiveLocalizationHomEquiv C X Y g := by
  apply ((kInjectiveLocalizationObject_rightOrthogonal C Y).map_bijective_of_isTriangulated
    DerivedCategory.Qh X').injective
  rw [Functor.map_comp, Qh_map_kInjectiveLocalizationHomEquiv,
    Qh_map_kInjectiveLocalizationHomEquiv, Category.assoc]

/--
概要：非有界導来局所化の右随伴となる K-injective 模型関手。
方針：自然な Hom 比較から関手の射部分を構成する。
規約：対象の分解の存在は既に証明済み。
使われ方：TT §3、Toën §3.2、Stacks 19.12.6 の非有界右導来関手。
-/
def kInjectiveLocalizationRightAdjoint : DerivedCategory C ⥤ HomotopyCategory C (.up ℤ) :=
  Adjunction.rightAdjointOfEquiv (kInjectiveLocalizationHomEquiv C)
    (kInjectiveLocalizationHomEquiv_naturality C)

/--
概要：Mathlib の非有界導来局所化と K-injective 模型は随伴する。
方針：構成した自然な Hom 比較の随伴を取る。
規約：元の導来圏と局所化を保つ。
使われ方：TT §3、Toën §3.2 の右導来関手の普遍性。
-/
def kInjectiveLocalizationAdjunction : DerivedCategory.Qh ⊣ kInjectiveLocalizationRightAdjoint C :=
  Adjunction.adjunctionOfEquivRight (kInjectiveLocalizationHomEquiv C)
    (kInjectiveLocalizationHomEquiv_naturality C)

end SerrePositivity.KST.DerivedGeometry
