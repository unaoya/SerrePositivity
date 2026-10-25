module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorAlgebraDiagonal
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrimitiveComparison
/-!
概要：元の自由対象対角の全 Hom 作用を、Milnor fiber の指定比較に一致させる。
方針：元の二射影と零比較を回収し、元の gluing Hom の三成分一意性を使う。
規約：準同型な別の鎖写像への置換ではなく、元の dg 関手の作用を照合する。
使われ方：同じ対角の一回 Perf 延長の充満忠実性へ進むために用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
open KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => dgAlgebraCategory R d.source
local notation "C" => dgAlgebraCategory R d.left
local notation "D" => dgAlgebraCategory R d.right
local notation "E" => dgAlgebraCategory R d.corner
local notation "p" => dgAlgebraMap R d.lower
local notation "q" => dgAlgebraMap R d.upper
local notation "L" => dgAlgebraMap R d.top
local notation "G" => dgAlgebraMap R d.side
local notation "M" => dgHomGluingBimodule R (C) (D) (E) (p) (q)
local notation "X" => dgGluingMilnorGenerator R d
local notation "F" => dgGluingMilnorAlgebraDiagonal R d
lemma dgGluingMilnorAlgebraDiagonal_map_left (x y : P) :
    (F).map x y ≫ dgGluingLeftHomMap R (C) (D) (M) (X) (X) = d.top.hom := by
  have h : HEq (((F).comp (dgGluingLeft R (C) (D) (M))).map x y) ((L).map x y) := by
    rw [dgGluingMilnorAlgebraDiagonal_left]
  exact eq_of_heq h
lemma dgGluingMilnorAlgebraDiagonal_map_right (x y : P) :
    (F).map x y ≫ dgGluingRightHomMap R (C) (D) (M) (X) (X) = d.side.hom := by
  have h : HEq (((F).comp (dgGluingRight R (C) (D) (M))).map x y) ((G).map x y) := by
    rw [dgGluingMilnorAlgebraDiagonal_right]
  have hh := eq_of_heq h
  change (F).map x y ≫ (dgGluingRight R (C) (D) (M)).map (X) (X) = _ at hh
  rw [dgGluingRight_map] at hh
  exact hh
lemma dgGluingMilnorAlgebraDiagonal_map_comparison (x y : P) :
    dgGluingHomComparison R (C) (D) (M) (X) (X) d.source.X ((F).map x y) = 0 := by
  let μ := dgHomGluingComparisonCycle R (C) (D) (E) (p) (q) (L) (G) (fun _ => 𝟙 _)
  let hn := dgHomGluingComparison_naturality R (C) (D) (E) (p) (q) (L) (G)
    (fun _ => 𝟙 _) (dgGluingMilnorAlgebraDiagonal_naturality R d)
  let A := dgStrictGluingCommaFamily R (C) (D) (M) (L) (G) μ hn
  have hm : (F).map x y ≫ (dgGluingHomRepresentableIso R (C) (D) (M) (X) (X)).hom =
      A.toDGFunctor.map x y := by
    have h : HEq (((dgStrictGluingFunctor R (C) (D) (M) (L) (G) μ hn).comp
        (dgGluingToComma R (C) (D) (M))).map x y) (A.toDGFunctor.map x y) := by
      rw [dgStrictGluingFunctor_toComma]
    exact eq_of_heq h
  have h := dgGluingHomComparison_yoneda R (C) (D) (M) (X) (X) d.source.X ((F).map x y)
  rw [hm] at h
  change (dgFunctorCommaHomComparison R (D) (RightModule R (C)) (M).toFunctor
    (A.obj x) (A.obj y) d.source.X (A.homMap x y)).comp _ _ = _ at h
  erw [A.homMap_comparison x y, Cochain.zero_comp] at h
  exact h.symm
lemma dgGluingMilnorAlgebraDiagonal_map (x y : P) :
    (F).map x y = dgGluingMilnorGeneratorHomComparison R d := by
  apply dgGluingHom_ext R (C) (D) (M) (X) (X) d.source.X
  · exact (dgGluingMilnorAlgebraDiagonal_map_left R d x y).trans
      (dgGluingMilnorGeneratorHomComparison_left R d).symm
  · exact (dgGluingMilnorAlgebraDiagonal_map_right R d x y).trans
      (dgGluingMilnorGeneratorHomComparison_right R d).symm
  · exact (dgGluingMilnorAlgebraDiagonal_map_comparison R d x y).trans
      (dgGluingMilnorGeneratorHomComparison_primitive R d).symm
lemma dgGluingMilnorAlgebraDiagonal_homQuasiIso (h : DGGluingMilnorSquare R d) :
    HomQuasiIso (dgGluingMilnorAlgebraDiagonal R d) := by
  intro x y
  rw [dgGluingMilnorAlgebraDiagonal_map]
  exact dgGluingMilnorGeneratorHomComparison_quasiIso R d h
end SerrePositivity.InfinityCategories
