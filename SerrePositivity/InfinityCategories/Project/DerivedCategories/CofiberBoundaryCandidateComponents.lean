module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryCandidate
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # cofiber 候補の挿入成分と後続方程式

概要：左右の候補の二成分を共通の解に同定し、後続集合の微分方程式を証明する。
方針：置換成分の異種等号と右辺の保存を、Q の微分定理へ接続する。
規約：HA Proposition 1.3.1.10。使われ方：四つの未知方程式と共通面の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- Left 候補の suffix 成分は共通の Q cochain と異種等号で一致する。 -/
lemma cofiberBoundaryLeftCandidate_suffix_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card)
    (hx : x = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) x y k hI hx hy hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_suffix_heq _ _ _ x y k hI hx hy hk).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).1.property

/-- Left 候補の first 成分は共通の A cochain と異種等号で一致する。 -/
lemma cofiberBoundaryLeftCandidate_first_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hx : x = (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).hom
      (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_first_heq _ _ _ x y k hI hx hy hk).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).2.property

/-- Left 候補は後続集合で単体の微分方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_suffix_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).Equation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_apex f g b hb) rfl
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb)
  · exact cofiberBoundaryLeftCandidate_suffix_heq f g b hb _ _ _ _ _ _ _
  · change HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).spanSuffixRhs) _
    exact (heq_of_eq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b).spanInsertUnknowns_suffix_rhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).1.val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).2.val)).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0_heq f g b hb).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ_differential f g b hb

/-- Right 候補の suffix 成分は共通の Q cochain と異種等号で一致する。 -/
lemma cofiberBoundaryRightCandidate_suffix_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card)
    (hx : x = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) x y k hI hx hy hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_suffix_heq _ _ _ x y k hI hx hy hk).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).1.property

/-- Right 候補の first 成分は共通の A cochain と異種等号で一致する。 -/
lemma cofiberBoundaryRightCandidate_first_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hx : x = (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).hom
      (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_first_heq _ _ _ x y k hI hx hy hk).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).2.property

/-- Right 候補は後続集合で単体の微分方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_suffix_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).Equation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_apex f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b)
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb)
  · exact cofiberBoundaryRightCandidate_suffix_heq f g b hb _ _ _ _ _ _ _
  · change HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).spanSuffixRhs) _
    exact (heq_of_eq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).spanInsertUnknowns_suffix_rhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).1.val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).2.val)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0_heq_right f g b hb).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ_differential f g b hb

/-- 挿入した二集合以外では Left 候補の成分は零未知基底から変わらない。 -/
lemma cofiberBoundaryLeftCandidate_hom_of_ne {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hy : y = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hq : I ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (ha : I ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).hom I x y k hI hx hy hk =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b).hom I x y k hI hx hy hk :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_hom_of_ne _ _ _ I x y k hI hx hy hk hq ha

/-- 挿入した二集合以外では Right 候補の成分は零未知基底から変わらない。 -/
lemma cofiberBoundaryRightCandidate_hom_of_ne {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hy : y = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hq : I ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (ha : I ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).hom I x y k hI hx hy hk =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).hom I x y k hI hx hy hk :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_hom_of_ne _ _ _ I x y k hI hx hy hk hq ha

/-- 集合の等号も含めた Left 候補の suffix 成分の比較。 -/
lemma cofiberBoundaryLeftCandidate_suffix_heq_of_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hEq : I = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hy : y = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).hom I x y k hI hx hy hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) := by
  cases hEq
  exact cofiberBoundaryLeftCandidate_suffix_heq f g b hb x y k hI hx hy hk

/-- 集合の等号も含めた Left 候補の first 成分の比較。 -/
lemma cofiberBoundaryLeftCandidate_first_heq_of_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hEq : I = insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hy : y = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).hom I x y k hI hx hy hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb) := by
  cases hEq
  exact cofiberBoundaryLeftCandidate_first_heq f g b hb x y k hI hx hy hk

/-- 集合の等号も含めた Right 候補の suffix 成分の比較。 -/
lemma cofiberBoundaryRightCandidate_suffix_heq_of_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hEq : I = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hy : y = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).hom I x y k hI hx hy hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) := by
  cases hEq
  exact cofiberBoundaryRightCandidate_suffix_heq f g b hb x y k hI hx hy hk

/-- 集合の等号も含めた Right 候補の first 成分の比較。 -/
lemma cofiberBoundaryRightCandidate_first_heq_of_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hEq : I = insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hy : y = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).hom I x y k hI hx hy hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb) := by
  cases hEq
  exact cofiberBoundaryRightCandidate_first_heq f g b hb x y k hI hx hy hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories
