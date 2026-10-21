module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceUnderFamilies
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-!
概要：反復 coslice と展開した図式の coslice の厳密な同型と射影の一致。
方針：元の固定図式と可変終点を同じ join の再結合で保持する。
規約：充填条件を追加仮定しない。使われ方：HTT 5.5.4 の局所同値の pushout 保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K L X A A' : SSet.{u}} {p : K ⟶ X} (q : L ⟶ sliceUnder p)

/-- 反復 coslice と展開した図式の coslice への族の全単射。 -/
def iteratedSliceUnderHomEquiv (A : SSet.{u}) :
    (A ⟶ sliceUnder q) ≃ (A ⟶ sliceUnder (sliceUnderUncurry q)) where
  toFun := iteratedSliceUnderForwardFamily q
  invFun := iteratedSliceUnderBackwardFamily q
  left_inv := iteratedSliceUnderFamily_backward_forward q
  right_inv := iteratedSliceUnderFamily_forward_backward q

/-- 恒等族から得た反復 coslice の標準比較射。 -/
def iteratedSliceUnderMap : sliceUnder q ⟶ sliceUnder (sliceUnderUncurry q) :=
  iteratedSliceUnderForwardFamily q (𝟙 (sliceUnder q))

/-- 順方向の族は標準比較射への後合成に一致する。 -/
lemma iteratedSliceUnderForwardFamily_eq (s : A ⟶ sliceUnder q) :
    iteratedSliceUnderForwardFamily q s = s ≫ iteratedSliceUnderMap q := by
  simpa only [Category.comp_id, iteratedSliceUnderMap] using
    iteratedSliceUnderForwardFamily_naturality q s (𝟙 (sliceUnder q))

/-- 同じ二重 curry から得た標準逆射。 -/
def iteratedSliceUnderInv : sliceUnder (sliceUnderUncurry q) ⟶ sliceUnder q :=
  iteratedSliceUnderBackwardFamily q (𝟙 (sliceUnder (sliceUnderUncurry q)))

/-- 逆方向の族は標準逆射への後合成に一致する。 -/
lemma iteratedSliceUnderBackwardFamily_eq (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    iteratedSliceUnderBackwardFamily q s = s ≫ iteratedSliceUnderInv q := by
  simpa only [Category.comp_id, iteratedSliceUnderInv] using
    iteratedSliceUnderBackwardFamily_naturality q s (𝟙 (sliceUnder (sliceUnderUncurry q)))

/-- 反復 coslice は元の展開した図式の coslice と厳密に同型。 -/
def iteratedSliceUnderIso : sliceUnder q ≅ sliceUnder (sliceUnderUncurry q) where
  hom := iteratedSliceUnderMap q
  inv := iteratedSliceUnderInv q
  hom_inv_id := by
    rw [← iteratedSliceUnderBackwardFamily_eq]
    exact iteratedSliceUnderFamily_backward_forward q (𝟙 (sliceUnder q))
  inv_hom_id := by
    rw [← iteratedSliceUnderForwardFamily_eq]
    exact iteratedSliceUnderFamily_forward_backward q (𝟙 (sliceUnder (sliceUnderUncurry q)))

/-- 順方向は二重の可変終点の射影を保つ。 -/
lemma iteratedSliceUnderForwardFamily_projection (s : A ⟶ sliceUnder q) :
    iteratedSliceUnderForwardFamily q s ≫ sliceUnderProjection (sliceUnderUncurry q) =
      s ≫ sliceUnderProjection q ≫ sliceUnderProjection p := by
  rw [← sliceUnderUncurry_projection (iteratedSliceUnderForwardFamily q s),
    iteratedSliceUnderForwardFamily_uncurry, ← Category.assoc, joinAssociator_last,
    Category.assoc, sliceUnderUncurry_projection, ← Category.assoc,
    sliceUnderUncurry_projection, Category.assoc]

/-- 標準同型は元の値域への二重の射影と可換。 -/
lemma iteratedSliceUnderIso_projection :
    (iteratedSliceUnderIso q).hom ≫ sliceUnderProjection (sliceUnderUncurry q) =
      sliceUnderProjection q ≫ sliceUnderProjection p := by
  simpa only [Category.id_comp, iteratedSliceUnderIso, iteratedSliceUnderMap] using
    iteratedSliceUnderForwardFamily_projection q (𝟙 (sliceUnder q))

end SerrePositivity.InfinityCategories.HomotopyLimits
