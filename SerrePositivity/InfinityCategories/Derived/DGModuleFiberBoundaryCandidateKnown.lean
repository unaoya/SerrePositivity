module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryCandidate

/-! # 標準 fiber の候補データの既知部分

概要：二成分を挿入した候補は全ての既知の面・方程式と残りの零未知成分を保存する。
方針：二つの置換集合は先頭集合を含むので、既知面のどの頂点も飛ばさない。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：残る検証を四未知集合の方程式に限定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：Left 側候補の対象族は元の零未知データと同じ。
方針：成分置換は対象を変えない。
規約：HA Proposition 1.3.1.10。使われ方：回収済みの対象・辺の同定を再利用する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_obj {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) (i : Fin (n + 4)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).obj i = (dgModuleFiberBoundaryLeftBase A D f
      b).obj i := rfl

/-- 概要：Left 側候補は全ての先頭頂点を飛ばした既知の面で元のデータに一致する。
方針：置換する二集合はいずれも飛ばした頂点を含み、面の像には現れない。
規約：HA Proposition 1.3.1.10。使われ方：元の slice 境界との一致。 -/
lemma dgModuleFiberBoundaryLeftCandidate_pullback_face {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (j : Fin (n + 4)) (hj : j ∈ cospanPrefixFaces n) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).pullback j.succAboveOrderEmb.toOrderHom =
      (dgModuleFiberBoundaryLeftBase A D f b).pullback j.succAboveOrderEmb.toOrderHom := by
  unfold dgModuleFiberBoundaryLeftCandidate SimplexData.replaceFixed
  rw [SimplexData.replace_pullback_of_omits _ _ _ _ j (Finset.mem_insert_of_mem hj)
    (fun x => Fin.succAbove_ne j x)]
  exact SimplexData.replace_pullback_of_omits _ _ _ _ j hj (fun x => Fin.succAbove_ne j x)

/-- 概要：Left 側候補は全ての既知集合で方程式を満たす。
方針：置換集合を含まない集合の方程式の保存を二回適用する。
規約：HA Proposition 1.3.1.10。使われ方：候補の未知方程式だけを個別に検証する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (I : Finset (Fin (n + 4))) (hI : ¬ cospanPrefixFaces n ⊆ I) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).Equation I := by
  unfold dgModuleFiberBoundaryLeftCandidate SimplexData.replaceFixed
  apply SimplexData.equation_replace_of_not_subset
  · intro hsub
    exact hI ((Finset.subset_insert _ _).trans hsub)
  · exact SimplexData.equation_replace_of_not_subset _ _ _ I hI
      (dgModuleFiberBoundaryLeftBase_equation A D f b I hI)

/-- 概要：Left 側候補は指定した二集合以外の成分を保存する。
方針：集合の相違による成分の置換公式を二回適用する。
規約：HA Proposition 1.3.1.10。使われ方：残りの未知成分の零性と既知辺の保存。 -/
lemma dgModuleFiberBoundaryLeftCandidate_hom_of_ne {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (I : Finset (Fin (n + 4))) (h0 : I ≠ cospanPrefixFaces n)
    (hD : I ≠ insert (cospanLastTail n) (cospanPrefixFaces n))
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).hom I a c k hI ha hc hk =
      (dgModuleFiberBoundaryLeftBase A D f b).hom I a c k hI ha hc hk := by
  unfold dgModuleFiberBoundaryLeftCandidate SimplexData.replaceFixed
  rw [SimplexData.replace_hom_of_ne _ _ _ I a c k hI ha hc hk hD,
    SimplexData.replace_hom_of_ne _ _ _ I a c k hI ha hc hk h0]

/-- 概要：Left 側候補の先頭・N 側以外の未知成分は零。
方針：二集合以外の成分の保存と零未知基底の零性を使う。
規約：HA Proposition 1.3.1.10。使われ方：b,c,e,f を零に取る明示解の実現。 -/
lemma dgModuleFiberBoundaryLeftCandidate_unknown_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (I : Finset (Fin (n + 4))) (hprefix : cospanPrefixFaces n ⊆ I)
    (h0 : I ≠ cospanPrefixFaces n)
    (hD : I ≠ insert (cospanLastTail n) (cospanPrefixFaces n))
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).hom I a c k hI ha hc hk = 0 := by
  rw [dgModuleFiberBoundaryLeftCandidate_hom_of_ne A D f b hb I h0 hD a c k hI ha hc hk]
  exact dgModuleFiberBoundaryLeftBase_unknownHom A D f b I hprefix a c k hI ha hc hk

/-- 概要：Right 側候補の対象族は元の零未知データと同じ。
方針：成分置換は対象を変えない。
規約：HA Proposition 1.3.1.10。使われ方：回収済みの対象・辺の同定を再利用する。 -/
lemma dgModuleFiberBoundaryRightCandidate_obj {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) (i : Fin (n + 4)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).obj i = (dgModuleFiberBoundaryRightBase A D f
      b).obj i := rfl

/-- 概要：Right 側候補は全ての先頭頂点を飛ばした既知の面で元のデータに一致する。
方針：置換する二集合はいずれも飛ばした頂点を含み、面の像には現れない。
規約：HA Proposition 1.3.1.10。使われ方：元の slice 境界との一致。 -/
lemma dgModuleFiberBoundaryRightCandidate_pullback_face {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (j : Fin (n + 4)) (hj : j ∈ cospanPrefixFaces n) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).pullback j.succAboveOrderEmb.toOrderHom =
      (dgModuleFiberBoundaryRightBase A D f b).pullback j.succAboveOrderEmb.toOrderHom := by
  unfold dgModuleFiberBoundaryRightCandidate SimplexData.replaceFixed
  rw [SimplexData.replace_pullback_of_omits _ _ _ _ j (Finset.mem_insert_of_mem hj)
    (fun x => Fin.succAbove_ne j x)]
  exact SimplexData.replace_pullback_of_omits _ _ _ _ j hj (fun x => Fin.succAbove_ne j x)

/-- 概要：Right 側候補は全ての既知集合で方程式を満たす。
方針：置換集合を含まない集合の方程式の保存を二回適用する。
規約：HA Proposition 1.3.1.10。使われ方：候補の未知方程式だけを個別に検証する。 -/
lemma dgModuleFiberBoundaryRightCandidate_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (I : Finset (Fin (n + 4))) (hI : ¬ cospanPrefixFaces n ⊆ I) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).Equation I := by
  unfold dgModuleFiberBoundaryRightCandidate SimplexData.replaceFixed
  apply SimplexData.equation_replace_of_not_subset
  · intro hsub
    exact hI ((Finset.subset_insert _ _).trans hsub)
  · exact SimplexData.equation_replace_of_not_subset _ _ _ I hI
      (dgModuleFiberBoundaryRightBase_equation A D f b I hI)

/-- 概要：Right 側候補は指定した二集合以外の成分を保存する。
方針：集合の相違による成分の置換公式を二回適用する。
規約：HA Proposition 1.3.1.10。使われ方：残りの未知成分の零性と既知辺の保存。 -/
lemma dgModuleFiberBoundaryRightCandidate_hom_of_ne {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (I : Finset (Fin (n + 4))) (h0 : I ≠ cospanPrefixFaces n)
    (hD : I ≠ insert (cospanLastTail n) (cospanPrefixFaces n))
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).hom I a c k hI ha hc hk =
      (dgModuleFiberBoundaryRightBase A D f b).hom I a c k hI ha hc hk := by
  unfold dgModuleFiberBoundaryRightCandidate SimplexData.replaceFixed
  rw [SimplexData.replace_hom_of_ne _ _ _ I a c k hI ha hc hk hD,
    SimplexData.replace_hom_of_ne _ _ _ I a c k hI ha hc hk h0]

/-- 概要：Right 側候補の先頭・N 側以外の未知成分は零。
方針：二集合以外の成分の保存と零未知基底の零性を使う。
規約：HA Proposition 1.3.1.10。使われ方：b,c,e,f を零に取る明示解の実現。 -/
lemma dgModuleFiberBoundaryRightCandidate_unknown_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (I : Finset (Fin (n + 4))) (hprefix : cospanPrefixFaces n ⊆ I)
    (h0 : I ≠ cospanPrefixFaces n)
    (hD : I ≠ insert (cospanLastTail n) (cospanPrefixFaces n))
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).hom I a c k hI ha hc hk = 0 := by
  rw [dgModuleFiberBoundaryRightCandidate_hom_of_ne A D f b hb I h0 hD a c k hI ha hc hk]
  exact dgModuleFiberBoundaryRightBase_unknownHom A D f b I hprefix a c k hI ha hc hk

end SerrePositivity.InfinityCategories
