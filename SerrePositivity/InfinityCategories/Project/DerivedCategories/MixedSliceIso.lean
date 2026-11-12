module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MixedSliceFamilies
/-!
概要：coslice 内の slice と slice 内の coslice の交換を厳密な単体集合同型にする。
方針：全族の往復則とパラメータ自然性を恒等族に適用する。
規約：充填性も可逆性も仮定しない。使われ方：固定外側二因子を持つ実三角形の共通模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
variable {K L X A A' : SSet.{u}} {p : K ⟶ X} (q : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)
/-- 混合 slice の交換は、任意の実パラメータ変更と厳密に可換。 -/
lemma mixedSliceForwardFamily_naturality (v : A' ⟶ A) (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q (v ≫ s) = v ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily_uncurry, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardInner_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily_uncurry,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardInner_uncurry, ← Category.assoc, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_naturality]
/-- 逆交換も、任意の実パラメータ変更と厳密に可換。 -/
lemma mixedSliceBackwardFamily_naturality (v : A' ⟶ A)
    (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceBackwardFamily q (v ≫ s) = v ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceBackwardFamily q s := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceBackwardFamily q (v ≫ s)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q (v ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceBackwardFamily q s) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceFamily_forward_backward, mixedSliceForwardFamily_naturality,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceFamily_forward_backward]
  have h' := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceBackwardFamily q) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceFamily_backward_forward] using h'
/-- 混合 slice の任意の全族の厳密な全単射。 -/
def mixedSliceHomEquiv (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q) ≃ (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q)) where
  toFun := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q
  invFun := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceBackwardFamily q
  left_inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceFamily_backward_forward q
  right_inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceFamily_forward_backward q
/-- 混合 slice の交換の標準射。 -/
def mixedSliceMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q (𝟙 _)
/-- 混合 slice の交換の標準逆射。 -/
def mixedSliceInv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceBackwardFamily q (𝟙 _)
/-- 順方向の全族の交換は、同じ標準射への後合成。 -/
lemma mixedSliceForwardFamily_eq (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q s = s ≫ mixedSliceMap q := by
  simpa only [Category.comp_id, mixedSliceMap] using
    mixedSliceForwardFamily_naturality q s (𝟙 _)
/-- 逆方向の全族の交換も、同じ標準逆射への後合成。 -/
lemma mixedSliceBackwardFamily_eq (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceBackwardFamily q s = s ≫ mixedSliceInv q := by
  simpa only [Category.comp_id, mixedSliceInv] using
    mixedSliceBackwardFamily_naturality q s (𝟙 _)
/-- coslice 内の slice は、同じ固定全図式の slice 内の coslice と厳密に同型。 -/
def mixedSliceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q) where
  hom := mixedSliceMap q
  inv := mixedSliceInv q
  hom_inv_id := by
    rw [← mixedSliceBackwardFamily_eq]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceFamily_backward_forward q (𝟙 _)
  inv_hom_id := by
    rw [← mixedSliceForwardFamily_eq]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceFamily_forward_backward q (𝟙 _)
/-- 固定二因子の転置は、元の固定始点図式を厳密に射影する。 -/
lemma mixedSliceTranspose_projection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) = p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]
/-- 交換した全族は、中間因子の元の同じ X への射影を保つ。 -/
lemma mixedSliceForwardFamily_projection (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) =
        s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  rw [← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily q s),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardFamily_uncurry, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardInner q s),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceForwardInner_uncurry, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A) L),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_leftPair, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection,
    Category.assoc]
/-- 混合 slice の厳密同型は、中間因子の元の同じ X への射影と可換。 -/
lemma mixedSliceIso_projection :
    (mixedSliceIso q).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mixedSliceTranspose q) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  simpa only [mixedSliceIso, mixedSliceMap, Category.id_comp] using
    mixedSliceForwardFamily_projection q (𝟙 _)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
