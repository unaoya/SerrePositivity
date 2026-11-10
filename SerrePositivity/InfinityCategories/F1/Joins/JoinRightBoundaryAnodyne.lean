module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinRightBoundaryCorner
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.JoinRightColimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：left anodyne な右因子に対する join の相対境界の inner anodyne 性。
方針：単射を像の部分複体へ移し、空の左部分複体との pushout-join に同定する。
規約：左因子は任意。
使われ方：Kerodon Example 4.3.6.5、Theorem 5.3.5.7 の有限鎖の帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：空の左 join の単位同型は右因子の射に自然。
方針：右包含の自然性を単位同型の逆射で打ち消す。
規約：空因子は K の空部分複体。
使われ方：Kerodon Example 4.3.6.5、右因子の相対境界の表示。 -/
lemma emptyJoinIso_naturality {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    joinMap (𝟙 ((⊥ : K.Subcomplex) : SSet.{u})) f ≫ (emptyJoinIso K B).hom =
      (emptyJoinIso K A).hom ≫ f := by
  apply (cancel_epi (emptyJoinIso K A).inv).1
  rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap]
  simp only [Category.assoc, ← emptyJoinIso_inv, Iso.inv_hom_id,
    Category.comp_id, Iso.inv_hom_id_assoc]

/-- 概要：右部分複体の相対境界は空の左部分複体との pushout-join の pushout を与える。
方針：空の左 join の単位同型で既存の正方形を移送する。
規約：右下の対象は二つの像の和の部分複体。
使われ方：Kerodon Example 4.3.6.5、任意の単射への移送。 -/
lemma joinRightBoundary_subcomplex_isPushout {B : SSet.{u}} (A : B.Subcomplex) (K : SSet.{u}) :
    IsPushout (joinInr K (A : SSet.{u})) A.ι
      (joinUnionRight (⊥ : K.Subcomplex) A)
      ((emptyJoinIso K B).inv ≫ joinUnionLeft (⊥ : K.Subcomplex) A) := by
  apply (joinUnion_isPushout (⊥ : K.Subcomplex) A).flip.of_iso
    (emptyJoinIso K (A : SSet.{u})) (Iso.refl _) (emptyJoinIso K B) (Iso.refl _)
  · apply (cancel_epi (emptyJoinIso K (A : SSet.{u})).inv).1
    rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp]
    simp only [← emptyJoinIso_inv, Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  · exact emptyJoinIso_naturality A.ι K
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]

/-- 概要：left anodyne な単射の右 join の相対境界は inner anodyne。
方針：像への同型で部分複体版へ移し、pushout-join の inner anodyne 性を使う。
規約：単射性を明示的に仮定する。
使われ方：Kerodon Example 4.3.6.5、Theorem 5.3.5.7 の最初の辺と尾部の貼り合わせ。 -/
@[kerodon 0235]
lemma joinRightBoundaryMap_innerAnodyne_of_leftAnodyne {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (K : SSet.{u}) (hi : leftAnodyneExtensions i) :
    innerAnodyneExtensions (joinRightBoundaryMap i K) := by
  let R := Subfunctor.range i
  let e : A ≅ (R : SSet.{u}) := asIso (Subfunctor.toRange i)
  have he : e.hom ≫ R.ι = i := Subfunctor.toRange_ι i
  have hR : leftAnodyneExtensions R.ι := by
    rwa [← leftAnodyneExtensions.cancel_left_of_respectsIso e.hom, he]
  let hs := joinRightBoundary_subcomplex_isPushout R K
  let eK : join K (R : SSet.{u}) ≅ join K A := (joinRightFunctor K).mapIso e.symm
  have hp : IsPushout (joinInr K A) i
      (joinMap (𝟙 K) e.hom ≫ joinUnionRight (⊥ : K.Subcomplex) R)
      ((emptyJoinIso K B).inv ≫ joinUnionLeft (⊥ : K.Subcomplex) R) := by
    apply hs.of_iso e.symm eK (Iso.refl B) (Iso.refl _)
    · change joinInr K (R : SSet.{u}) ≫ joinMap (𝟙 K) e.inv = e.inv ≫ joinInr K A
      simpa only [Category.id_comp] using joinInr_joinMap (𝟙 K) e.inv
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · change joinUnionRight (⊥ : K.Subcomplex) R ≫ 𝟙 _ =
        joinMap (𝟙 K) e.inv ≫ (joinMap (𝟙 K) e.hom ≫ _)
      simp only [Category.comp_id, ← Category.assoc, ← joinMap_comp,
        Iso.inv_hom_id, Category.id_comp, joinMap_id]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have hm : joinRightBoundaryMap i K = hp.isoPushout.inv ≫ (joinUnion (⊥ : K.Subcomplex) R).ι := by
    apply pushout.hom_ext
    · rw [joinRightBoundaryMap_join, ← Category.assoc, hp.inl_isoPushout_inv,
        Category.assoc, joinUnionRight_ι, ← joinMap_comp, he, Category.id_comp]
    · rw [joinRightBoundaryMap_right, ← Category.assoc, hp.inr_isoPushout_inv,
        Category.assoc, joinUnionLeft_ι, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp]
  rw [hm, innerAnodyneExtensions.cancel_left_of_respectsIso]
  exact joinUnion_innerAnodyne_of_leftAnodyne (⊥ : K.Subcomplex) R hR

end SerrePositivity.InfinityCategories
