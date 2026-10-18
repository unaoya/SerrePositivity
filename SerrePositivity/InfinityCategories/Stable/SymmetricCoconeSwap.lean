module
public import SerrePositivity.InfinityCategories.Stable.FixedCosliceReindexUncurry
public import SerrePositivity.InfinityCategories.Stable.SuspensionFixedReindexSwap

/-! # 対称 span の余錐空間の交換作用

概要：同じ辺を二枝に使う span の余錐空間に、枝を交換する対合を構成する。
方針：固定図式内の再添字付けを特殊化し、二枝への制限と Hom 表示での作用を計算する。
規約：自己写像の型には図式の輸送を残さない。使われ方：二枝の引き戻しからループ反転への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同じ辺を二枝に使う span の余錐空間の二枝交換。
方針：二枝交換が図式を固定する等号で同じ図式上の自己作用を作る。
規約：辺の終点の零対象性は不要。使われ方：対称な suspension の写像空間での作用。 -/
def symmetricCoconeSwap {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    coconeMappingSpace (edgeSpan f f) y ⟶ coconeMappingSpace (edgeSpan f f) y :=
  fixedCoconeMappingReindex (edgeSpan f f) spanSwap (edgeSpan_self_swap f) y

/-- 概要：対称 span の二枝交換は二度で恒等になる。
方針：形状の交換の対合性を固定図式の再添字付けへ適用する。
規約：値域の充填性は不要。使われ方：交換作用の自己同型性。 -/
lemma symmetricCoconeSwap_comp_self {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    symmetricCoconeSwap f y ≫ symmetricCoconeSwap f y = 𝟙 _ :=
  fixedCoconeMappingReindex_comp_self _ _ _ spanSwap_comp_self y

/-- 概要：対称 span の二枝交換による余錐空間の自己同型。
方針：交換自体を逆に使う。
規約：実際の単体集合の同型。使われ方：写像空間の自己作用の比較。 -/
def symmetricCoconeSwapIso {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    coconeMappingSpace (edgeSpan f f) y ≅ coconeMappingSpace (edgeSpan f f) y where
  hom := symmetricCoconeSwap f y
  inv := symmetricCoconeSwap f y
  hom_inv_id := symmetricCoconeSwap_comp_self f y
  inv_hom_id := symmetricCoconeSwap_comp_self f y

/-- 概要：交換後の余錐の第一枝は元の第二枝である。
方針：自己作用を展開して joinMap の合成に枝の交換則を使う。
規約：余錐族のパラメータは任意。使われ方：二枝の引き戻し模型での作用。 -/
lemma symmetricCoconeSwap_left {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (a : T ⟶ coconeMappingSpace (edgeSpan f f) y) :
    joinMap horn₂₀.ι₀₁ (𝟙 T) ≫ sliceUnderUncurry
      ((a ≫ symmetricCoconeSwap f y) ≫ vertexFiberι (sliceUnderProjection (edgeSpan f f)) y) =
    joinMap horn₂₀.ι₀₂ (𝟙 T) ≫ sliceUnderUncurry
      (a ≫ vertexFiberι (sliceUnderProjection (edgeSpan f f)) y) := by
  rw [symmetricCoconeSwap, fixedCoconeMappingReindex_uncurry, ← Category.assoc,
    ← joinMap_comp, spanSwap_left, Category.comp_id]

/-- 概要：交換後の余錐の第二枝は元の第一枝である。
方針：自己作用を展開して第二枝の交換則を使う。
規約：余錐族のパラメータは任意。使われ方：二枝の引き戻し模型での作用。 -/
lemma symmetricCoconeSwap_right {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (a : T ⟶ coconeMappingSpace (edgeSpan f f) y) :
    joinMap horn₂₀.ι₀₂ (𝟙 T) ≫ sliceUnderUncurry
      ((a ≫ symmetricCoconeSwap f y) ≫ vertexFiberι (sliceUnderProjection (edgeSpan f f)) y) =
    joinMap horn₂₀.ι₀₁ (𝟙 T) ≫ sliceUnderUncurry
      (a ≫ vertexFiberι (sliceUnderProjection (edgeSpan f f)) y) := by
  rw [symmetricCoconeSwap, fixedCoconeMappingReindex_uncurry, ← Category.assoc,
    ← joinMap_comp, spanSwap_right, Category.comp_id]

/-- 概要：対称 span の余錐空間の交換は Hom 表示で標準頂点自己同型の前合成となる。
方針：固定図式の再添字付けの Hom への作用を二枝交換へ特殊化する。
規約：値域は quasicategory、c は指定した図式の余極限余錐。使われ方：交換作用と負号の比較。 -/
lemma symmetricCoconeSwap_piZero {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (c : JoinCocone (edgeSpan f f)) (hc : IsColimitCone c) (y : X _⦋0⦌)
    (a : SSet.π₀ (coconeMappingSpace (edgeSpan f f) y)) :
    coconeMappingSpacePiZeroEquiv c hc y (SSet.mapπ₀ (symmetricCoconeSwap f y) a) =
      (fixedCoconeReindexVertexIso c hc spanSwap (edgeSpan_self_swap f) spanSwap_comp_self).hom ≫
        coconeMappingSpacePiZeroEquiv c hc y a :=
  coconeMappingSpacePiZeroEquiv_reindexFixed c hc spanSwap (edgeSpan_self_swap f)
    spanSwap_comp_self y a

end SerrePositivity.InfinityCategories
