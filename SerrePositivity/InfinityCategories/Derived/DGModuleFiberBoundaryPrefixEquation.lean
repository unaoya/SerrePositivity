module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryCandidateKnown
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # 候補データの先頭集合の方程式

概要：明示解を挿入した候補は先頭集合で単体の方程式を満たす。
方針：先頭右辺は二回の置換で変わらず、成分の微分は型付き解の微分式へ移す。
規約：HA Proposition 1.3.1.10。使われ方：四つの未知集合のうち最初の方程式の検証。
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

/-- 概要：N を加えた先頭集合は先頭集合に含まれない。
方針：D の頂点番号は先頭の最大値より大きい。
規約：HTT §1.2.13。使われ方：N 側成分の挿入が先頭の方程式を変えないこと。 -/
lemma cospanPrefix_insertLast_not_subset (n : ℕ) :
    ¬ insert (cospanLastTail n) (cospanPrefixFaces n) ⊆ cospanPrefixFaces n := by
  intro hsub
  have hle := (mem_cospanPrefixFaces_iff_le _).mp (hsub (Finset.mem_insert_self _ _))
  exact not_le_of_gt ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) hle

/-- 概要：Left 側候補の先頭成分は挿入した生の解に等しい。
方針：N 側集合との相違と先頭置換の自己評価を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭成分の微分の同定。 -/
lemma dgModuleFiberBoundaryLeftCandidate_prefix_hom {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : (0 : Fin (n + 4)) = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hc : cospanApex n = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : dgModuleFiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).hom (cospanPrefixFaces n) 0 (cospanApex n)
      (dgModuleFiberBoundaryDegree n + 1) hI ha hc hk = (dgModuleFiberBoundaryLeftNative A D f b
        hb).1.val := by
  have hne : cospanPrefixFaces n ≠ insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    apply cospanPrefix_insertLast_not_subset n
    rw [← heq]
  unfold dgModuleFiberBoundaryLeftCandidate
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne]
  exact SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 概要：Left 側候補の先頭右辺は零未知基底の先頭右辺から変わらない。
方針：N 側置換の局所性と先頭置換の自己右辺の保存を使う。
規約：HA Proposition 1.3.1.10。使われ方：型付きの r₀ をそのまま先頭方程式に使う。 -/
lemma dgModuleFiberBoundaryLeftCandidate_prefix_rhs {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : (0 : Fin (n + 4)) = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hc : cospanApex n = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : dgModuleFiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).rhs (cospanPrefixFaces n) 0 (cospanApex n)
      (dgModuleFiberBoundaryDegree n + 1) hI ha hc hk =
      (dgModuleFiberBoundaryLeftBase A D f b).rhs (cospanPrefixFaces n) 0 (cospanApex n)
        (dgModuleFiberBoundaryDegree n + 1) hI ha hc hk := by
  unfold dgModuleFiberBoundaryLeftCandidate
  rw [SimplexData.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (cospanPrefix_insertLast_not_subset n)]
  exact SimplexData.replaceFixed_rhs_self _ _ _ _ _ _ _ _ _ _

/-- 概要：Left 側候補は先頭集合で単体の方程式を満たす。
方針：保存された右辺と挿入した成分を型付き r₀,a へ異種等号で移し、δa=r₀ を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭の未知方程式の検証。 -/
lemma dgModuleFiberBoundaryLeftCandidate_prefix_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).Equation (cospanPrefixFaces n) := by
  have hI : 2 ≤ (cospanPrefixFaces n).card := by rw [card_cospanPrefixFaces]; omega
  have hk : dgModuleFiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ) := by
    rw [card_cospanPrefixFaces]
    dsimp only [dgModuleFiberBoundaryDegree]
    push_cast
    omega
  apply SimplexData.equation_of_fixed_heq (dgModuleFiberBoundaryLeftCandidate A D f b hb)
    (cospanPrefixFaces n) 0 (cospanApex n)
    (dgModuleFiberBoundaryDegree n + 1) hI (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
      hk
    rfl (dgModuleFiberBoundary_left_apex A D f b hb) rfl
    (dgModuleFiberBoundaryUnknownA A D f b hb) (dgModuleFiberBoundaryRhs0 A D f b hb)
  · exact (heq_of_eq (dgModuleFiberBoundaryLeftCandidate_prefix_hom A D f b hb hI _ _ hk)).trans
      (dgModuleFiberBoundaryLeftNative A D f b hb).1.property
  · rw [dgModuleFiberBoundaryLeftCandidate_prefix_rhs A D f b hb hI _ _ hk]
    exact ((dgModuleFiberBoundaryLeftBase A D f b).rhs_heq_of_degrees _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryRhs0_heq_raw A D f b hb).symm
  · exact dgModuleFiberBoundaryUnknownA_differential A D f b hb

/-- 概要：Right 側候補の先頭成分は挿入した生の解に等しい。
方針：N 側集合との相違と先頭置換の自己評価を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭成分の微分の同定。 -/
lemma dgModuleFiberBoundaryRightCandidate_prefix_hom {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : (0 : Fin (n + 4)) = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hc : cospanApex n = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : dgModuleFiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).hom (cospanPrefixFaces n) 0 (cospanApex n)
      (dgModuleFiberBoundaryDegree n + 1) hI ha hc hk = (dgModuleFiberBoundaryRightNative A D f b
        hb).1.val := by
  have hne : cospanPrefixFaces n ≠ insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    apply cospanPrefix_insertLast_not_subset n
    rw [← heq]
  unfold dgModuleFiberBoundaryRightCandidate
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne]
  exact SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 概要：Right 側候補の先頭右辺は零未知基底の先頭右辺から変わらない。
方針：N 側置換の局所性と先頭置換の自己右辺の保存を使う。
規約：HA Proposition 1.3.1.10。使われ方：型付きの r₀ をそのまま先頭方程式に使う。 -/
lemma dgModuleFiberBoundaryRightCandidate_prefix_rhs {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : (0 : Fin (n + 4)) = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hc : cospanApex n = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : dgModuleFiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).rhs (cospanPrefixFaces n) 0 (cospanApex n)
      (dgModuleFiberBoundaryDegree n + 1) hI ha hc hk =
      (dgModuleFiberBoundaryRightBase A D f b).rhs (cospanPrefixFaces n) 0 (cospanApex n)
        (dgModuleFiberBoundaryDegree n + 1) hI ha hc hk := by
  unfold dgModuleFiberBoundaryRightCandidate
  rw [SimplexData.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (cospanPrefix_insertLast_not_subset n)]
  exact SimplexData.replaceFixed_rhs_self _ _ _ _ _ _ _ _ _ _

/-- 概要：Right 側候補は先頭集合で単体の方程式を満たす。
方針：保存された右辺と挿入した成分を型付き r₀,a へ異種等号で移し、δa=r₀ を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭の未知方程式の検証。 -/
lemma dgModuleFiberBoundaryRightCandidate_prefix_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).Equation (cospanPrefixFaces n) := by
  have hI : 2 ≤ (cospanPrefixFaces n).card := by rw [card_cospanPrefixFaces]; omega
  have hk : dgModuleFiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ) := by
    rw [card_cospanPrefixFaces]
    dsimp only [dgModuleFiberBoundaryDegree]
    push_cast
    omega
  apply SimplexData.equation_of_fixed_heq (dgModuleFiberBoundaryRightCandidate A D f b hb)
    (cospanPrefixFaces n) 0 (cospanApex n)
    (dgModuleFiberBoundaryDegree n + 1) hI (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
      hk
    (dgModuleFiberBoundarySource_right_eq A D f b) (dgModuleFiberBoundary_right_apex A D f b hb) rfl
    (dgModuleFiberBoundaryUnknownA A D f b hb) (dgModuleFiberBoundaryRhs0 A D f b hb)
  · exact (heq_of_eq (dgModuleFiberBoundaryRightCandidate_prefix_hom A D f b hb hI _ _ hk)).trans
      (dgModuleFiberBoundaryRightNative A D f b hb).1.property
  · rw [dgModuleFiberBoundaryRightCandidate_prefix_rhs A D f b hb hI _ _ hk]
    exact ((dgModuleFiberBoundaryRightBase A D f b).rhs_heq_of_degrees _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryRhs0_heq_right A D f b hb).symm
  · exact dgModuleFiberBoundaryUnknownA_differential A D f b hb

end SerrePositivity.InfinityCategories
