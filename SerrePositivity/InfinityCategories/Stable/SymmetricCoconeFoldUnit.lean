module
public import SerrePositivity.InfinityCategories.Stable.SymmetricSpanFold

/-! # 畳み込んだ余錐と対角のループ単位

概要：一本の辺の余錐を二枝に複写した余錐は、自己引き戻し表示で対角となり、ループの単位を表す。
方針：両枝への制限が恒等であることを展開した余錐で計算する。
規約：値域の充填性や零対象性は不要。使われ方：ループ単位の零射への因子分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：一本の辺の余錐を畳み込みで二枝に送り第一枝へ戻すと元の余錐。
方針：展開した族で、第一枝の後の畳み込みが恒等であることを使う。
規約：任意の終点についての射の等号。使われ方：自己引き戻し表示の第一成分。 -/
lemma symmetricCoconeFold_first {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    symmetricCoconeFold f y ≫ symmetricCoconeFirst f y = 𝟙 _ := by
  apply vertexFiber_hom_ext
  apply sliceUnderUncurry_injective
  have H := symmetricCoconeFold_uncurry f y (𝟙 _)
  simp only [Category.id_comp] at H
  rw [symmetricCoconeFirst_uncurry, H]
  simp only [← Category.assoc, ← joinMap_comp, spanFold_left, Category.id_comp,
    joinMap_id, Category.id_comp]
  rfl

/-- 概要：一本の辺の余錐を畳み込みで二枝に送り第二枝へ戻すと元の余錐。
方針：展開した族で、第二枝の後の畳み込みが恒等であることを使う。
規約：第一枝と同じ余錐となる。使われ方：自己引き戻し表示の第二成分。 -/
lemma symmetricCoconeFold_second {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    symmetricCoconeFold f y ≫ symmetricCoconeSecond f y = 𝟙 _ := by
  apply vertexFiber_hom_ext
  apply sliceUnderUncurry_injective
  have H := symmetricCoconeFold_uncurry f y (𝟙 _)
  simp only [Category.id_comp] at H
  rw [symmetricCoconeSecond_uncurry, H]
  simp only [← Category.assoc, ← joinMap_comp, spanFold_right, Category.id_comp,
    joinMap_id, Category.id_comp]
  rfl

/-- 概要：畳んだ余錐の自己引き戻し表示は枝の余錐の対角となる。
方針：両射影で恒等成分を照合する。
規約：実際の単体的な射の等号。使われ方：単位の代表元を同定する。 -/
lemma symmetricCoconeFold_kernelPair {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    symmetricCoconeFold f y ≫ (symmetricCoconeKernelPairIso f y).hom =
      kanKernelPairDiagonal (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, symmetricCoconeKernelPairIso_hom_fst,
      symmetricCoconeFold_first, kanKernelPairDiagonal_fst]
  · simp only [Category.assoc, symmetricCoconeKernelPairIso_hom_snd,
      symmetricCoconeFold_second, kanKernelPairDiagonal_snd]

/-- 概要：枝の基点を畳み込みで全体へ送った成分がループの単位である。
方針：自己引き戻し表示の単射性、対角の式、単位の定義を使う。
規約：値域の充填性や枝の終点の始対象性は不要。使われ方：単位の Hom 表示を畳んだ余錐で計算する。 -/
lemma symmetricCoconeLoopUnit_eq_fold {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (e : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    symmetricCoconeLoopUnit f y e = SSet.mapπ₀ (symmetricCoconeFold f y) (SSet.π₀.mk e) := by
  apply stableMapPiZeroIso_injective (symmetricCoconeKernelPairIso f y)
  rw [symmetricCoconeLoopUnit_kernelPair, ← SSet.mapπ₀_comp_apply, symmetricCoconeFold_kernelPair]

end SerrePositivity.InfinityCategories
