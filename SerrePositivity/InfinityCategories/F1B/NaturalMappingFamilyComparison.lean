module

public import SerrePositivity.InfinityCategories.F1B.MappingFamilyPresheaves

/-!
概要：ホモトピー族の前層の自然変換と coherent 矢印比較の対応。
方針：全端点の族の前層で自然性を指定し、普遍矢印の族への評価で射を回収する。
規約：単位・同値性は入力しない。パラメータ自然性は通常の自然変換である。
使われ方：B1 の自然性の具体的な表現定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：全端点のホモトピー族に作用する端点を保つ自然変換。
方針：族の前層間の自然変換と二つの射影への整合を保持する。
規約：各点で独立な対応の族ではなく、任意のパラメータ射に自然。
使われ方：coherent な自然対応を矢印空間に依存せず指定する型。 -/
structure NaturalMappingFamilyComparison {X Y : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ X) where
  transformation : leftMappingFamilyPresheaf F ⟶ rightMappingFamilyPresheaf G
  source : transformation ≫ rightMappingFamilySource G = leftMappingFamilySource F
  target : transformation ≫ rightMappingFamilyTarget G = leftMappingFamilyTarget F

/-- 概要：族の自然比較は自然変換の等式で決まる。
方針：構造の外延性と proof irrelevance を使う。
規約：射影の証明の比較は不要。使われ方：表示の両逆。 -/
lemma NaturalMappingFamilyComparison.ext_transformation {X Y : SSet.{u}}
    {F : X ⟶ Y} {G : Y ⟶ X} {q r : NaturalMappingFamilyComparison F G}
    (h : q.transformation = r.transformation) : q = r := by
  cases q
  cases r
  cases h
  rfl

/-- 概要：矢印比較は単体的な射の等式で決まる。
方針：構造の外延性と proof irrelevance を使う。
規約：射影の証明の比較は不要。使われ方：表示の両逆。 -/
lemma MappingArrowComparison.ext_map {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
    {q r : MappingArrowComparison F G} (h : q.map = r.map) : q = r := by
  cases q
  cases r
  cases h
  rfl

namespace MappingArrowComparison
variable {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}

/-- 概要：矢印空間の比較は全端点の族の前層の自然変換を与える。
方針：表現可能性の自然同型で Yoneda による後合成を移す。
規約：元の両端の射影を厳密に保つ。使われ方：自然比較の表現定理の順方向。 -/
def toNaturalMappingFamilyComparison (q : MappingArrowComparison F G) :
    NaturalMappingFamilyComparison F G where
  transformation := (leftMappingFamilyPresheafIso F).inv ≫ yoneda.map q.map ≫
    (rightMappingFamilyPresheafIso G).hom
  source := by
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro f
    change ((leftMappingFamilyEquiv F A.unop).symm f ≫ q.map) ≫ unitCommaSource G = f.source
    rw [Category.assoc, q.source]
    exact leftMappingArrowLift_source _ _ _ _
  target := by
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro f
    change ((leftMappingFamilyEquiv F A.unop).symm f ≫ q.map) ≫ unitCommaTarget G = f.target
    rw [Category.assoc, q.target]
    exact leftMappingArrowLift_target _ _ _ _

end MappingArrowComparison
namespace NaturalMappingFamilyComparison
variable {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
variable (q : NaturalMappingFamilyComparison F G)

/-- 概要：前層の自然な族の比較を普遍矢印の族に評価して射を得る。
方針：矢印空間自体をパラメータに取り、恒等射の族の像を表示する。
規約：単位は指定しない。使われ方：自然比較の表現定理の逆方向。 -/
def toMappingArrowComparison : MappingArrowComparison F G where
  map := (rightMappingFamilyEquiv G _).symm
    (q.transformation.app (Opposite.op (leftMappingArrow F))
      (leftMappingFamilyEquiv F _ (𝟙 _)))
  source := by
    rw [show (rightMappingFamilyEquiv G _).symm _ ≫ unitCommaSource G = _ from
      unitCommaLift_source _ _ _ _]
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app q.source (Opposite.op (leftMappingArrow F)))
      (leftMappingFamilyEquiv F _ (𝟙 _))
    change _ = (𝟙 (leftMappingArrow F)) ≫ leftMappingArrowSource F at h
    exact h.trans (Category.id_comp _)
  target := by
    rw [show (rightMappingFamilyEquiv G _).symm _ ≫ unitCommaTarget G = _ from
      unitCommaLift_target _ _ _ _]
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app q.target (Opposite.op (leftMappingArrow F)))
      (leftMappingFamilyEquiv F _ (𝟙 _))
    change _ = (𝟙 (leftMappingArrow F)) ≫ leftMappingArrowTarget F at h
    exact h.trans (Category.id_comp _)

/-- 概要：回収した矢印の射は自然変換の任意のパラメータ成分を表す。
方針：任意の族を普遍族の引き戻しと見て、自然性を適用する。
規約：端点図式は任意、等式はホモトピー類を取る前の族の等式。
使われ方：表示定理の完全性と独立な族の選択の排除。 -/
lemma transformation_app (A : SSet.{u}) (f : LeftMappingFamily F A) :
    q.transformation.app (Opposite.op A) f =
      rightMappingFamilyEquiv G A ((leftMappingFamilyEquiv F A).symm f ≫
        q.toMappingArrowComparison.map) := by
  let i := (leftMappingFamilyEquiv F A).symm f
  have h := ConcreteCategory.congr_hom
    (q.transformation.naturality i.op) (leftMappingFamilyEquiv F _ (𝟙 _))
  change q.transformation.app (Opposite.op A)
    (leftMappingFamilyEquiv F A (i ≫
      (leftMappingFamilyEquiv F _).symm (leftMappingFamilyEquiv F _ (𝟙 _)))) =
    rightMappingFamilyEquiv G A (i ≫ q.toMappingArrowComparison.map) at h
  rw [Equiv.symm_apply_apply, Category.comp_id, Equiv.apply_symm_apply] at h
  exact h

/-- 概要：自然変換を矢印の射へ移して戻すと元の自然変換。
方針：任意のパラメータでの表示公式と自然変換の外延性を使う。
規約：射影の証明は proof irrelevance で消す。使われ方：表示の両逆。 -/
lemma toMappingArrowComparison_toNatural :
    q.toMappingArrowComparison.toNaturalMappingFamilyComparison = q := by
  have ht : q.toMappingArrowComparison.toNaturalMappingFamilyComparison.transformation =
      q.transformation := by
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro f
    exact (q.transformation_app A.unop f).symm
  exact NaturalMappingFamilyComparison.ext_transformation ht

end NaturalMappingFamilyComparison

/-- 概要：矢印比較を自然変換へ移して普遍族で回収すると元の射。
方針：表現可能性の両逆と恒等射の後合成を使う。
規約：全単体的な射の厳密な回収。使われ方：表示の両逆。 -/
lemma MappingArrowComparison.toNaturalMappingFamilyComparison_toMappingArrow
    {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X} (q : MappingArrowComparison F G) :
    q.toNaturalMappingFamilyComparison.toMappingArrowComparison = q := by
  have hm : q.toNaturalMappingFamilyComparison.toMappingArrowComparison.map = q.map := by
    change (rightMappingFamilyEquiv G _).symm
      (rightMappingFamilyEquiv G _ ((leftMappingFamilyEquiv F _).symm
        (leftMappingFamilyEquiv F _ (𝟙 _)) ≫ q.map)) = q.map
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Category.id_comp]
  exact MappingArrowComparison.ext_map hm

/-- 概要：coherent 矢印比較と端点を保つ族の前層の自然変換は全単射。
方針：普遍族への評価と Yoneda による後合成の厳密な両逆を束ねる。
規約：同値性も単位も仮定しない。使われ方：B1 の自然性の具体的な表現定理。 -/
def mappingArrowNaturalFamilyEquiv {X Y : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ X) :
    MappingArrowComparison F G ≃ NaturalMappingFamilyComparison F G where
  toFun := MappingArrowComparison.toNaturalMappingFamilyComparison
  invFun := NaturalMappingFamilyComparison.toMappingArrowComparison
  left_inv := MappingArrowComparison.toNaturalMappingFamilyComparison_toMappingArrow
  right_inv := NaturalMappingFamilyComparison.toMappingArrowComparison_toNatural

end SerrePositivity.InfinityCategories
