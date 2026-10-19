module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryCandidate
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # cofiber 候補の挿入成分と後続方程式

概要：左右の候補の二成分を共通の解に同定し、後続集合の微分方程式を証明する。
方針：置換成分の異種等号と右辺の保存を、Q の微分定理へ接続する。
規約：HA Proposition 1.3.1.10。使われ方：四つの未知方程式と共通面の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- Left 候補の suffix 成分は共通の Q cochain と異種等号で一致する。 -/
lemma dgModuleConeBoundaryLeftCandidate_suffix_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (spanSuffixFaces n).card)
    (hx : x = (spanSuffixFaces n).min' (Index.nonempty hI))
    (hy : y = (spanSuffixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((spanSuffixFaces n).card : ℤ)) :
    HEq ((dgModuleConeBoundaryLeftCandidate A D f b hb).hom (spanSuffixFaces n) x y k hI hx hy hk)
      (dgModuleConeBoundaryLiftQ A D f b hb) :=
  (SimplexData.spanInsertUnknowns_suffix_heq _ _ _ x y k hI hx hy hk).trans
    (dgModuleConeBoundaryLeftNative A D f b hb).1.property

/-- Left 候補の first 成分は共通の A cochain と異種等号で一致する。 -/
lemma dgModuleConeBoundaryLeftCandidate_first_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (insert 0 (spanSuffixFaces n)).card)
    (hx : x = (insert 0 (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert 0 (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert 0 (spanSuffixFaces n)).card : ℤ)) :
    HEq ((dgModuleConeBoundaryLeftCandidate A D f b hb).hom
      (insert 0 (spanSuffixFaces n)) x y k hI hx hy hk)
      (dgModuleConeBoundaryLiftA A D f b hb) :=
  (SimplexData.spanInsertUnknowns_first_heq _ _ _ x y k hI hx hy hk).trans
    (dgModuleConeBoundaryLeftNative A D f b hb).2.property

/-- Left 候補は後続集合で単体の微分方程式を満たす。 -/
lemma dgModuleConeBoundaryLeftCandidate_suffix_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).Equation (spanSuffixFaces n) := by
  apply SimplexData.equation_of_fixed_heq (dgModuleConeBoundaryLeftCandidate A D f b hb)
    (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [card_spanSuffixFaces]; omega)
    (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
    (by rw [card_spanSuffixFaces]; push_cast; omega)
    (dgModuleConeBoundary_left_apex A D f b hb) rfl
    (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    (dgModuleConeBoundaryLiftQ A D f b hb) (dgModuleConeBoundaryRhs0 A D f b hb)
  · exact dgModuleConeBoundaryLeftCandidate_suffix_heq A D f b hb _ _ _ _ _ _ _
  · change HEq ((dgModuleConeBoundaryLeftCandidate A D f b hb).spanSuffixRhs) _
    exact (heq_of_eq ((dgModuleConeBoundaryLeftBase A D f b).spanInsertUnknowns_suffix_rhs
      (dgModuleConeBoundaryLeftNative A D f b hb).1.val
      (dgModuleConeBoundaryLeftNative A D f b hb).2.val)).trans (dgModuleConeBoundaryRhs0_heq A
        D f b hb).symm
  · exact dgModuleConeBoundaryLiftQ_differential A D f b hb

/-- Right 候補の suffix 成分は共通の Q cochain と異種等号で一致する。 -/
lemma dgModuleConeBoundaryRightCandidate_suffix_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (spanSuffixFaces n).card)
    (hx : x = (spanSuffixFaces n).min' (Index.nonempty hI))
    (hy : y = (spanSuffixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((spanSuffixFaces n).card : ℤ)) :
    HEq ((dgModuleConeBoundaryRightCandidate A D f b hb).hom (spanSuffixFaces n) x y k hI hx hy hk)
      (dgModuleConeBoundaryLiftQ A D f b hb) :=
  (SimplexData.spanInsertUnknowns_suffix_heq _ _ _ x y k hI hx hy hk).trans
    (dgModuleConeBoundaryRightNative A D f b hb).1.property

/-- Right 候補の first 成分は共通の A cochain と異種等号で一致する。 -/
lemma dgModuleConeBoundaryRightCandidate_first_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (insert 0 (spanSuffixFaces n)).card)
    (hx : x = (insert 0 (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert 0 (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert 0 (spanSuffixFaces n)).card : ℤ)) :
    HEq ((dgModuleConeBoundaryRightCandidate A D f b hb).hom
      (insert 0 (spanSuffixFaces n)) x y k hI hx hy hk)
      (dgModuleConeBoundaryLiftA A D f b hb) :=
  (SimplexData.spanInsertUnknowns_first_heq _ _ _ x y k hI hx hy hk).trans
    (dgModuleConeBoundaryRightNative A D f b hb).2.property

/-- Right 候補は後続集合で単体の微分方程式を満たす。 -/
lemma dgModuleConeBoundaryRightCandidate_suffix_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).Equation (spanSuffixFaces n) := by
  apply SimplexData.equation_of_fixed_heq (dgModuleConeBoundaryRightCandidate A D f b hb)
    (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [card_spanSuffixFaces]; omega)
    (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
    (by rw [card_spanSuffixFaces]; push_cast; omega)
    (dgModuleConeBoundary_right_apex A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b)
    (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    (dgModuleConeBoundaryLiftQ A D f b hb) (dgModuleConeBoundaryRhs0 A D f b hb)
  · exact dgModuleConeBoundaryRightCandidate_suffix_heq A D f b hb _ _ _ _ _ _ _
  · change HEq ((dgModuleConeBoundaryRightCandidate A D f b hb).spanSuffixRhs) _
    exact (heq_of_eq ((dgModuleConeBoundaryRightBase A D f b).spanInsertUnknowns_suffix_rhs
      (dgModuleConeBoundaryRightNative A D f b hb).1.val
      (dgModuleConeBoundaryRightNative A D f b hb).2.val)).trans
      (dgModuleConeBoundaryRhs0_heq_right A D f b hb).symm
  · exact dgModuleConeBoundaryLiftQ_differential A D f b hb

/-- 挿入した二集合以外では Left 候補の成分は零未知基底から変わらない。 -/
lemma dgModuleConeBoundaryLeftCandidate_hom_of_ne {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hq : I ≠ spanSuffixFaces n) (ha : I ≠ insert 0 (spanSuffixFaces n)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).hom I x y k hI hx hy hk =
      (dgModuleConeBoundaryLeftBase A D f b).hom I x y k hI hx hy hk :=
  SimplexData.spanInsertUnknowns_hom_of_ne _ _ _ I x y k hI hx hy hk hq ha

/-- 挿入した二集合以外では Right 候補の成分は零未知基底から変わらない。 -/
lemma dgModuleConeBoundaryRightCandidate_hom_of_ne {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hq : I ≠ spanSuffixFaces n) (ha : I ≠ insert 0 (spanSuffixFaces n)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).hom I x y k hI hx hy hk =
      (dgModuleConeBoundaryRightBase A D f b).hom I x y k hI hx hy hk :=
  SimplexData.spanInsertUnknowns_hom_of_ne _ _ _ I x y k hI hx hy hk hq ha

/-- 集合の等号も含めた Left 候補の suffix 成分の比較。 -/
lemma dgModuleConeBoundaryLeftCandidate_suffix_heq_of_eq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) (hEq : I = spanSuffixFaces n)
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((dgModuleConeBoundaryLeftCandidate A D f b hb).hom I x y k hI hx hy hk)
      (dgModuleConeBoundaryLiftQ A D f b hb) := by
  cases hEq
  exact dgModuleConeBoundaryLeftCandidate_suffix_heq A D f b hb x y k hI hx hy hk

/-- 集合の等号も含めた Left 候補の first 成分の比較。 -/
lemma dgModuleConeBoundaryLeftCandidate_first_heq_of_eq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) (hEq : I = insert 0 (spanSuffixFaces n))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((dgModuleConeBoundaryLeftCandidate A D f b hb).hom I x y k hI hx hy hk)
      (dgModuleConeBoundaryLiftA A D f b hb) := by
  cases hEq
  exact dgModuleConeBoundaryLeftCandidate_first_heq A D f b hb x y k hI hx hy hk

/-- 集合の等号も含めた Right 候補の suffix 成分の比較。 -/
lemma dgModuleConeBoundaryRightCandidate_suffix_heq_of_eq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) (hEq : I = spanSuffixFaces n)
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((dgModuleConeBoundaryRightCandidate A D f b hb).hom I x y k hI hx hy hk)
      (dgModuleConeBoundaryLiftQ A D f b hb) := by
  cases hEq
  exact dgModuleConeBoundaryRightCandidate_suffix_heq A D f b hb x y k hI hx hy hk

/-- 集合の等号も含めた Right 候補の first 成分の比較。 -/
lemma dgModuleConeBoundaryRightCandidate_first_heq_of_eq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) (hEq : I = insert 0 (spanSuffixFaces n))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((dgModuleConeBoundaryRightCandidate A D f b hb).hom I x y k hI hx hy hk)
      (dgModuleConeBoundaryLiftA A D f b hb) := by
  cases hEq
  exact dgModuleConeBoundaryRightCandidate_first_heq A D f b hb x y k hI hx hy hk

end SerrePositivity.InfinityCategories
