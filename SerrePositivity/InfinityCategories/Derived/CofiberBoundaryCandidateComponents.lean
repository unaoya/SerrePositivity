module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryCandidate
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # cofiber 候補の挿入成分と後続方程式

概要：左右の候補の二成分を共通の解に同定し、後続集合の微分方程式を証明する。
方針：置換成分の異種等号と右辺の保存を、Q の微分定理へ接続する。
規約：HA Proposition 1.3.1.10。使われ方：四つの未知方程式と共通面の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- Left 候補の suffix 成分は共通の Q cochain と異種等号で一致する。 -/
lemma cofiberBoundaryLeftCandidate_suffix_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (spanSuffixFaces n).card)
    (hx : x = (spanSuffixFaces n).min' (Index.nonempty hI))
    (hy : y = (spanSuffixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((spanSuffixFaces n).card : ℤ)) :
    HEq ((cofiberBoundaryLeftCandidate f g b hb).hom (spanSuffixFaces n) x y k hI hx hy hk)
      (cofiberBoundaryLiftQ f g b hb) :=
  (SimplexData.spanInsertUnknowns_suffix_heq _ _ _ x y k hI hx hy hk).trans
    (cofiberBoundaryLeftNative f g b hb).1.property

/-- Left 候補の first 成分は共通の A cochain と異種等号で一致する。 -/
lemma cofiberBoundaryLeftCandidate_first_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (insert 0 (spanSuffixFaces n)).card)
    (hx : x = (insert 0 (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert 0 (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert 0 (spanSuffixFaces n)).card : ℤ)) :
    HEq ((cofiberBoundaryLeftCandidate f g b hb).hom
      (insert 0 (spanSuffixFaces n)) x y k hI hx hy hk)
      (cofiberBoundaryLiftA f g b hb) :=
  (SimplexData.spanInsertUnknowns_first_heq _ _ _ x y k hI hx hy hk).trans
    (cofiberBoundaryLeftNative f g b hb).2.property

/-- Left 候補は後続集合で単体の微分方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_suffix_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryLeftCandidate f g b hb).Equation (spanSuffixFaces n) := by
  apply SimplexData.equation_of_fixed_heq (cofiberBoundaryLeftCandidate f g b hb)
    (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [card_spanSuffixFaces]; omega)
    (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
    (by rw [card_spanSuffixFaces]; push_cast; omega)
    (cofiberCosliceBoundary_left_apex f g b hb) rfl
    (by dsimp only [cofiberBoundaryDegree]; omega)
    (cofiberBoundaryLiftQ f g b hb) (cofiberBoundaryRhs0 f g b hb)
  · exact cofiberBoundaryLeftCandidate_suffix_heq f g b hb _ _ _ _ _ _ _
  · change HEq ((cofiberBoundaryLeftCandidate f g b hb).spanSuffixRhs) _
    exact (heq_of_eq ((cofiberBoundaryLeftBase f g b).spanInsertUnknowns_suffix_rhs
      (cofiberBoundaryLeftNative f g b hb).1.val
      (cofiberBoundaryLeftNative f g b hb).2.val)).trans (cofiberBoundaryRhs0_heq f g b hb).symm
  · exact cofiberBoundaryLiftQ_differential f g b hb

/-- Right 候補の suffix 成分は共通の Q cochain と異種等号で一致する。 -/
lemma cofiberBoundaryRightCandidate_suffix_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (spanSuffixFaces n).card)
    (hx : x = (spanSuffixFaces n).min' (Index.nonempty hI))
    (hy : y = (spanSuffixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((spanSuffixFaces n).card : ℤ)) :
    HEq ((cofiberBoundaryRightCandidate f g b hb).hom (spanSuffixFaces n) x y k hI hx hy hk)
      (cofiberBoundaryLiftQ f g b hb) :=
  (SimplexData.spanInsertUnknowns_suffix_heq _ _ _ x y k hI hx hy hk).trans
    (cofiberBoundaryRightNative f g b hb).1.property

/-- Right 候補の first 成分は共通の A cochain と異種等号で一致する。 -/
lemma cofiberBoundaryRightCandidate_first_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (insert 0 (spanSuffixFaces n)).card)
    (hx : x = (insert 0 (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert 0 (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert 0 (spanSuffixFaces n)).card : ℤ)) :
    HEq ((cofiberBoundaryRightCandidate f g b hb).hom
      (insert 0 (spanSuffixFaces n)) x y k hI hx hy hk)
      (cofiberBoundaryLiftA f g b hb) :=
  (SimplexData.spanInsertUnknowns_first_heq _ _ _ x y k hI hx hy hk).trans
    (cofiberBoundaryRightNative f g b hb).2.property

/-- Right 候補は後続集合で単体の微分方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_suffix_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryRightCandidate f g b hb).Equation (spanSuffixFaces n) := by
  apply SimplexData.equation_of_fixed_heq (cofiberBoundaryRightCandidate f g b hb)
    (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [card_spanSuffixFaces]; omega)
    (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
    (by rw [card_spanSuffixFaces]; push_cast; omega)
    (cofiberCosliceBoundary_right_apex f g b hb) (cofiberBoundaryTarget_right_eq f g b)
    (by dsimp only [cofiberBoundaryDegree]; omega)
    (cofiberBoundaryLiftQ f g b hb) (cofiberBoundaryRhs0 f g b hb)
  · exact cofiberBoundaryRightCandidate_suffix_heq f g b hb _ _ _ _ _ _ _
  · change HEq ((cofiberBoundaryRightCandidate f g b hb).spanSuffixRhs) _
    exact (heq_of_eq ((cofiberBoundaryRightBase f g b).spanInsertUnknowns_suffix_rhs
      (cofiberBoundaryRightNative f g b hb).1.val
      (cofiberBoundaryRightNative f g b hb).2.val)).trans
      (cofiberBoundaryRhs0_heq_right f g b hb).symm
  · exact cofiberBoundaryLiftQ_differential f g b hb

/-- 挿入した二集合以外では Left 候補の成分は零未知基底から変わらない。 -/
lemma cofiberBoundaryLeftCandidate_hom_of_ne {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hq : I ≠ spanSuffixFaces n) (ha : I ≠ insert 0 (spanSuffixFaces n)) :
    (cofiberBoundaryLeftCandidate f g b hb).hom I x y k hI hx hy hk =
      (cofiberBoundaryLeftBase f g b).hom I x y k hI hx hy hk :=
  SimplexData.spanInsertUnknowns_hom_of_ne _ _ _ I x y k hI hx hy hk hq ha

/-- 挿入した二集合以外では Right 候補の成分は零未知基底から変わらない。 -/
lemma cofiberBoundaryRightCandidate_hom_of_ne {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hq : I ≠ spanSuffixFaces n) (ha : I ≠ insert 0 (spanSuffixFaces n)) :
    (cofiberBoundaryRightCandidate f g b hb).hom I x y k hI hx hy hk =
      (cofiberBoundaryRightBase f g b).hom I x y k hI hx hy hk :=
  SimplexData.spanInsertUnknowns_hom_of_ne _ _ _ I x y k hI hx hy hk hq ha

/-- 集合の等号も含めた Left 候補の suffix 成分の比較。 -/
lemma cofiberBoundaryLeftCandidate_suffix_heq_of_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hEq : I = spanSuffixFaces n)
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((cofiberBoundaryLeftCandidate f g b hb).hom I x y k hI hx hy hk)
      (cofiberBoundaryLiftQ f g b hb) := by
  cases hEq
  exact cofiberBoundaryLeftCandidate_suffix_heq f g b hb x y k hI hx hy hk

/-- 集合の等号も含めた Left 候補の first 成分の比較。 -/
lemma cofiberBoundaryLeftCandidate_first_heq_of_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hEq : I = insert 0 (spanSuffixFaces n))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((cofiberBoundaryLeftCandidate f g b hb).hom I x y k hI hx hy hk)
      (cofiberBoundaryLiftA f g b hb) := by
  cases hEq
  exact cofiberBoundaryLeftCandidate_first_heq f g b hb x y k hI hx hy hk

/-- 集合の等号も含めた Right 候補の suffix 成分の比較。 -/
lemma cofiberBoundaryRightCandidate_suffix_heq_of_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hEq : I = spanSuffixFaces n)
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((cofiberBoundaryRightCandidate f g b hb).hom I x y k hI hx hy hk)
      (cofiberBoundaryLiftQ f g b hb) := by
  cases hEq
  exact cofiberBoundaryRightCandidate_suffix_heq f g b hb x y k hI hx hy hk

/-- 集合の等号も含めた Right 候補の first 成分の比較。 -/
lemma cofiberBoundaryRightCandidate_first_heq_of_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hEq : I = insert 0 (spanSuffixFaces n))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((cofiberBoundaryRightCandidate f g b hb).hom I x y k hI hx hy hk)
      (cofiberBoundaryLiftA f g b hb) := by
  cases hEq
  exact cofiberBoundaryRightCandidate_first_heq f g b hb x y k hI hx hy hk

end SerrePositivity.InfinityCategories
