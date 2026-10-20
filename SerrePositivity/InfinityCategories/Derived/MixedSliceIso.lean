module
public import SerrePositivity.InfinityCategories.Derived.MixedSliceFamilies
/-!
概要：coslice 内の slice と slice 内の coslice の交換を厳密な単体集合同型にする。
方針：全族の往復則とパラメータ自然性を恒等族に適用する。
規約：充填性も可逆性も仮定しない。使われ方：固定外側二因子を持つ実三角形の共通模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
variable {K L X A A' : SSet.{u}} {p : K ⟶ X} (q : L ⟶ sliceUnder p)
/-- 混合 slice の交換は、任意の実パラメータ変更と厳密に可換。 -/
lemma mixedSliceForwardFamily_naturality (v : A' ⟶ A) (s : A ⟶ sliceOver q) :
    mixedSliceForwardFamily q (v ≫ s) = v ≫ mixedSliceForwardFamily q s := by
  apply sliceUnderUncurry_injective (mixedSliceTranspose q)
  apply sliceOverUncurry_injective (q ≫ sliceUnderProjection p)
  rw [mixedSliceForwardFamily_uncurry, mixedSliceForwardInner_uncurry,
    sliceOverUncurry_precomp, sliceUnderUncurry_precomp, sliceUnderUncurry_precomp,
    sliceOverUncurry_precomp, mixedSliceForwardFamily_uncurry,
    mixedSliceForwardInner_uncurry, ← Category.assoc, ← Category.assoc,
    ← joinAssociator_naturality]
/-- 逆交換も、任意の実パラメータ変更と厳密に可換。 -/
lemma mixedSliceBackwardFamily_naturality (v : A' ⟶ A)
    (s : A ⟶ sliceUnder (mixedSliceTranspose q)) :
    mixedSliceBackwardFamily q (v ≫ s) = v ≫ mixedSliceBackwardFamily q s := by
  have h : mixedSliceForwardFamily q (mixedSliceBackwardFamily q (v ≫ s)) =
      mixedSliceForwardFamily q (v ≫ mixedSliceBackwardFamily q s) := by
    rw [mixedSliceFamily_forward_backward, mixedSliceForwardFamily_naturality,
      mixedSliceFamily_forward_backward]
  have h' := congrArg (mixedSliceBackwardFamily q) h
  simpa only [mixedSliceFamily_backward_forward] using h'
/-- 混合 slice の任意の全族の厳密な全単射。 -/
def mixedSliceHomEquiv (A : SSet.{u}) :
    (A ⟶ sliceOver q) ≃ (A ⟶ sliceUnder (mixedSliceTranspose q)) where
  toFun := mixedSliceForwardFamily q
  invFun := mixedSliceBackwardFamily q
  left_inv := mixedSliceFamily_backward_forward q
  right_inv := mixedSliceFamily_forward_backward q
/-- 混合 slice の交換の標準射。 -/
def mixedSliceMap : sliceOver q ⟶ sliceUnder (mixedSliceTranspose q) :=
  mixedSliceForwardFamily q (𝟙 _)
/-- 混合 slice の交換の標準逆射。 -/
def mixedSliceInv : sliceUnder (mixedSliceTranspose q) ⟶ sliceOver q :=
  mixedSliceBackwardFamily q (𝟙 _)
/-- 順方向の全族の交換は、同じ標準射への後合成。 -/
lemma mixedSliceForwardFamily_eq (s : A ⟶ sliceOver q) :
    mixedSliceForwardFamily q s = s ≫ mixedSliceMap q := by
  simpa only [Category.comp_id, mixedSliceMap] using
    mixedSliceForwardFamily_naturality q s (𝟙 _)
/-- 逆方向の全族の交換も、同じ標準逆射への後合成。 -/
lemma mixedSliceBackwardFamily_eq (s : A ⟶ sliceUnder (mixedSliceTranspose q)) :
    mixedSliceBackwardFamily q s = s ≫ mixedSliceInv q := by
  simpa only [Category.comp_id, mixedSliceInv] using
    mixedSliceBackwardFamily_naturality q s (𝟙 _)
/-- coslice 内の slice は、同じ固定全図式の slice 内の coslice と厳密に同型。 -/
def mixedSliceIso : sliceOver q ≅ sliceUnder (mixedSliceTranspose q) where
  hom := mixedSliceMap q
  inv := mixedSliceInv q
  hom_inv_id := by
    rw [← mixedSliceBackwardFamily_eq]
    exact mixedSliceFamily_backward_forward q (𝟙 _)
  inv_hom_id := by
    rw [← mixedSliceForwardFamily_eq]
    exact mixedSliceFamily_forward_backward q (𝟙 _)
/-- 固定二因子の転置は、元の固定始点図式を厳密に射影する。 -/
lemma mixedSliceTranspose_projection :
    mixedSliceTranspose q ≫ sliceOverProjection (q ≫ sliceUnderProjection p) = p := by
  rw [← sliceOverUncurry_projection, mixedSliceTranspose_uncurry, sliceUnderUncurry_fixed]
/-- 交換した全族は、中間因子の元の同じ X への射影を保つ。 -/
lemma mixedSliceForwardFamily_projection (s : A ⟶ sliceOver q) :
    mixedSliceForwardFamily q s ≫ sliceUnderProjection (mixedSliceTranspose q) ≫
      sliceOverProjection (q ≫ sliceUnderProjection p) =
        s ≫ sliceOverProjection q ≫ sliceUnderProjection p := by
  rw [← Category.assoc,
    ← sliceUnderUncurry_projection (mixedSliceForwardFamily q s),
    mixedSliceForwardFamily_uncurry, Category.assoc,
    ← sliceOverUncurry_projection (mixedSliceForwardInner q s),
    mixedSliceForwardInner_uncurry, ← Category.assoc (joinInl (join K A) L),
    joinAssociator_leftPair, ← Category.assoc (joinInr K A),
    joinInr_joinMap, Category.assoc,
    sliceUnderUncurry_projection, ← Category.assoc, sliceOverUncurry_projection,
    Category.assoc]
/-- 混合 slice の厳密同型は、中間因子の元の同じ X への射影と可換。 -/
lemma mixedSliceIso_projection :
    (mixedSliceIso q).hom ≫ sliceUnderProjection (mixedSliceTranspose q) ≫
      sliceOverProjection (q ≫ sliceUnderProjection p) =
        sliceOverProjection q ≫ sliceUnderProjection p := by
  simpa only [mixedSliceIso, mixedSliceMap, Category.id_comp] using
    mixedSliceForwardFamily_projection q (𝟙 _)
end SerrePositivity.InfinityCategories
