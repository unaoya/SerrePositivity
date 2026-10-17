module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundarySimplices

/-! # 候補データの挿入済み成分の異種等号

概要：先頭集合と D 側集合の成分は全ての端点・次数指定で共通の型付き解と異種等号で一致する。
方針：集合の等式を消去し、置換の評価と固定一射の移送を使う。
規約：HA Proposition 1.3.1.10。使われ方：左右の共通面で非零未知成分を同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：Left 側候補の prefix 成分は任意の有効な指定で共通の型付き解と異種等号で一致する。
方針：集合の同定、置換の評価、固定一射の移送の異種等号を組み合わせる。
規約：HA Construction 1.3.1.6。使われ方：共通面の成分の左右の比較。 -/
lemma fiberBoundaryLeftCandidate_prefix_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (I : Finset (Fin (n + 4))) (hEq : I = cospanPrefixFaces n)
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((fiberBoundaryLeftCandidate g h b hb).hom I a c k hI ha hc hk)
      (fiberBoundaryUnknownA g h b hb) := by
  cases hEq
  have hne : cospanPrefixFaces n ≠ insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    apply cospanPrefix_insertLast_not_subset n
    rw [← heq]
  unfold fiberBoundaryLeftCandidate SimplexData.replaceFixed
  rw [SimplexData.replace_hom_of_ne (hne := hne)]
  rw [SimplexData.replace_hom_same]
  exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
    (fiberBoundaryLeftNative g h b hb).1.property

/-- 概要：Left 側候補の last 成分は任意の有効な指定で共通の型付き解と異種等号で一致する。
方針：集合の同定、置換の評価、固定一射の移送の異種等号を組み合わせる。
規約：HA Construction 1.3.1.6。使われ方：共通面の成分の左右の比較。 -/
lemma fiberBoundaryLeftCandidate_last_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (I : Finset (Fin (n + 4))) (hEq : I = insert (cospanLastTail n) (cospanPrefixFaces n))
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((fiberBoundaryLeftCandidate g h b hb).hom I a c k hI ha hc hk)
      (fiberBoundaryUnknownD g h b hb) := by
  cases hEq
  unfold fiberBoundaryLeftCandidate SimplexData.replaceFixed
  rw [SimplexData.replace_hom_same]
  exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
    (fiberBoundaryLeftNative g h b hb).2.property

/-- 概要：Right 側候補の prefix 成分は任意の有効な指定で共通の型付き解と異種等号で一致する。
方針：集合の同定、置換の評価、固定一射の移送の異種等号を組み合わせる。
規約：HA Construction 1.3.1.6。使われ方：共通面の成分の左右の比較。 -/
lemma fiberBoundaryRightCandidate_prefix_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (I : Finset (Fin (n + 4))) (hEq : I = cospanPrefixFaces n)
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((fiberBoundaryRightCandidate g h b hb).hom I a c k hI ha hc hk)
      (fiberBoundaryUnknownA g h b hb) := by
  cases hEq
  have hne : cospanPrefixFaces n ≠ insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    apply cospanPrefix_insertLast_not_subset n
    rw [← heq]
  unfold fiberBoundaryRightCandidate SimplexData.replaceFixed
  rw [SimplexData.replace_hom_of_ne (hne := hne)]
  rw [SimplexData.replace_hom_same]
  exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
    (fiberBoundaryRightNative g h b hb).1.property

/-- 概要：Right 側候補の last 成分は任意の有効な指定で共通の型付き解と異種等号で一致する。
方針：集合の同定、置換の評価、固定一射の移送の異種等号を組み合わせる。
規約：HA Construction 1.3.1.6。使われ方：共通面の成分の左右の比較。 -/
lemma fiberBoundaryRightCandidate_last_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (I : Finset (Fin (n + 4))) (hEq : I = insert (cospanLastTail n) (cospanPrefixFaces n))
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((fiberBoundaryRightCandidate g h b hb).hom I a c k hI ha hc hk)
      (fiberBoundaryUnknownD g h b hb) := by
  cases hEq
  unfold fiberBoundaryRightCandidate SimplexData.replaceFixed
  rw [SimplexData.replace_hom_same]
  exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
    (fiberBoundaryRightNative g h b hb).2.property

end SerrePositivity.InfinityCategories.DGNerve
