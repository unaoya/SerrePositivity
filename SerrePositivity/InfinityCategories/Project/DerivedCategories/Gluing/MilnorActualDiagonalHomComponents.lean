module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorFreeHomComponents
/-!
概要：元小 Perf 対角の自由 Hom 作用から、同じ左右鎖写像と零比較を回収する。
方針：元の対角の射影等式と実 comma 表示を使う。
規約：元の対角写像の全三成分を保持する。
使われ方：Milnor 自由 Hom 同型と元対角作用の厳密な照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "D" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "V" => DGSmallPerfectSquareCorner R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "M" => dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS)
local notation "LS" => dgSmallPerfectArrow R (A) (C) (L)
local notation "GS" => dgSmallPerfectArrow R (A) (D) (G)
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d
local notation "X" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeObject R d
lemma dgGluingMilnorActualDiagonal_map_left :
    ((dgOdotQuotientInput R d).diagonal).map (b) (b) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R (CL) (DR) (M) (X) (X) =
      (LS).map (b) (b) := by
  have h : HEq
      ((((dgOdotQuotientInput R d).diagonal).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (CL) (DR) (M))).map (b) (b))
      ((LS).map (b) (b)) := by
    change HEq (((dgSmallPerfectSquareDiagonal R (A) (C) (D) (E) (L) (G) (p) (q)
      (dgOdotInput_dg_commutes R d)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (CL) (DR) (M))).map (b) (b)) _
    rw [dgSmallPerfectSquareDiagonal_left]
  exact eq_of_heq h
lemma dgGluingMilnorActualDiagonal_map_right :
    ((dgOdotQuotientInput R d).diagonal).map (b) (b) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R (CL) (DR) (M) (X) (X) =
      (GS).map (b) (b) := by
  have h : HEq
      ((((dgOdotQuotientInput R d).diagonal).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (CL) (DR) (M))).map (b) (b))
      ((GS).map (b) (b)) := by
    change HEq (((dgSmallPerfectSquareDiagonal R (A) (C) (D) (E) (L) (G) (p) (q)
      (dgOdotInput_dg_commutes R d)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (CL) (DR) (M))).map (b) (b)) _
    rw [dgSmallPerfectSquareDiagonal_right]
  have hh := eq_of_heq h
  change ((dgOdotQuotientInput R d).diagonal).map (b) (b) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (CL) (DR) (M)).map
    (X) (X) = _ at hh
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map] at hh
  exact hh
lemma dgGluingMilnorActualDiagonal_map_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison R (CL) (DR) (M) (X) (X)
      (homObject R (DGSmallPerfectBase R (A)) (b) (b)) (((dgOdotQuotientInput R d).diagonal).map
        (b) (b)) = 0 := by
  let a := fun x => (dgSmallPerfectSquareComparisonAt R (A) (C) (D) (E)
    (L) (G) (p) (q) (dgOdotInput_dg_commutes R d) x).hom
  let hn0 := dgSmallPerfectSquareComparisonAt_naturality R (A) (C) (D) (E)
    (L) (G) (p) (q) (dgOdotInput_dg_commutes R d)
  let μ := dgHomGluingComparisonCycle R (CL) (DR) (V) (pS) (qS) (LS) (GS) a
  let hn := dgHomGluingComparison_naturality R (CL) (DR) (V) (pS) (qS) (LS) (GS) a hn0
  let T := dgStrictGluingCommaFamily R (CL) (DR) (M) (LS) (GS) μ hn
  have hm : ((dgOdotQuotientInput R d).diagonal).map (b) (b) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R (CL) (DR) (M) (X) (X)).hom =
      T.toDGFunctor.map (b) (b) := by
    have h : HEq (((dgStrictGluingFunctor R (CL) (DR) (M) (LS) (GS) μ hn).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R (CL) (DR) (M))).map (b) (b)) (T.toDGFunctor.map (b) (b)) := by
      rw [dgStrictGluingFunctor_toComma]
    exact eq_of_heq h
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison_yoneda R (CL) (DR) (M) (X) (X)
    (homObject R (DGSmallPerfectBase R (A)) (b) (b)) (((dgOdotQuotientInput R d).diagonal).map (b)
      (b))
  rw [hm] at h
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R (DR) (RightModule R (CL)) (M).toFunctor
    (T.obj (b)) (T.obj (b)) _ (T.homMap (b) (b))).comp _ _ = _ at h
  erw [T.homMap_comparison (b) (b), Cochain.zero_comp] at h
  exact h.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
