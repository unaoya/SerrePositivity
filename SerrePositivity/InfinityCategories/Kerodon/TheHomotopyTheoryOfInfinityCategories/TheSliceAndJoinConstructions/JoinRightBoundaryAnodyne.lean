module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinRightBoundaryCorner
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightColimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：left anodyne な右因子に対する join の相対境界の inner anodyne 性。
方針：単射を像の部分複体へ移し、空の左部分複体との pushout-join に同定する。
規約：左因子は任意。
使われ方：Kerodon Example 4.3.6.5（Tag 0235）、Theorem 5.3.5.7（Tag 037Q） の有限鎖の帰納。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：空の左 join の単位同型は右因子の射に自然。
方針：右包含の自然性を単位同型の逆射で打ち消す。
規約：空因子は K の空部分複体。
使われ方：Kerodon Example 4.3.6.5（Tag 0235）、右因子の相対境界の表示。 -/
lemma emptyJoinIso_naturality {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 ((⊥ : K.Subcomplex) : SSet.{u})) f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K B).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K A).hom ≫ f := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K A).inv).1
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.emptyJoinIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]
  simp only [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.emptyJoinIso_inv, Iso.inv_hom_id,
    Category.comp_id, Iso.inv_hom_id_assoc]

/-- 概要：右部分複体の相対境界は空の左部分複体との pushout-join の pushout を与える。
方針：空の左 join の単位同型で既存の正方形を移送する。
規約：右下の対象は二つの像の和の部分複体。
使われ方：Kerodon Example 4.3.6.5（Tag 0235）、任意の単射への移送。 -/
lemma joinRightBoundary_subcomplex_isPushout {B : SSet.{u}} (A : B.Subcomplex) (K : SSet.{u}) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (A : SSet.{u})) A.ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (⊥ : K.Subcomplex) A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K B).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (⊥ : K.Subcomplex) A) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout (⊥ : K.Subcomplex) A).flip.of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K (A : SSet.{u})) (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K B) (Iso.refl _)
  · apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K (A : SSet.{u})).inv).1
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.emptyJoinIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    simp only [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.emptyJoinIso_inv, Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  · exact emptyJoinIso_naturality A.ι K
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]

/-- 概要：left anodyne な単射の右 join の相対境界は inner anodyne。
方針：像への同型で部分複体版へ移し、pushout-join の inner anodyne 性を使う。
規約：単射性を明示的に仮定する。
使われ方：Kerodon Example 4.3.6.5（Tag 0235）、Theorem 5.3.5.7（Tag 037Q） の最初の辺と尾部の貼り合わせ。 -/
@[kerodon 0235]
lemma joinRightBoundaryMap_innerAnodyne_of_leftAnodyne {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (K : SSet.{u}) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) :
    innerAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap i K) := by
  let R := Subfunctor.range i
  let e : A ≅ (R : SSet.{u}) := asIso (Subfunctor.toRange i)
  have he : e.hom ≫ R.ι = i := Subfunctor.toRange_ι i
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions R.ι := by
    rwa [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.cancel_left_of_respectsIso e.hom, he]
  let hs := joinRightBoundary_subcomplex_isPushout R K
  let eK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (R : SSet.{u}) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightFunctor K).mapIso e.symm
  have hp : IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A) i
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (⊥ : K.Subcomplex) R)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K B).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (⊥ : K.Subcomplex) R) := by
    apply hs.of_iso e.symm eK (Iso.refl B) (Iso.refl _)
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (R : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) e.inv = e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A
      simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap (𝟙 K) e.inv
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (⊥ : K.Subcomplex) R ≫ 𝟙 _ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) e.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) e.hom ≫ _)
      simp only [Category.comp_id, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
        Iso.inv_hom_id, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap i K = hp.isoPushout.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (⊥ : K.Subcomplex) R).ι := by
    apply pushout.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_join, ← Category.assoc, hp.inl_isoPushout_inv,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, he, Category.id_comp]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_right, ← Category.assoc, hp.inr_isoPushout_inv,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.emptyJoinIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
  rw [hm, innerAnodyneExtensions.cancel_left_of_respectsIso]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_leftAnodyne (⊥ : K.Subcomplex) R hR

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
