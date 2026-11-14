module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.MilnorAlgebraDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.PrimitiveComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
open KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "M" => dgHomGluingBimodule R (C) (D) (E) (p) (q)
local notation "X" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorAlgebraDiagonal R d
lemma dgGluingMilnorAlgebraDiagonal_map_left (x y : P) :
    (F).map x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R (C) (D) (M) (X) (X) = d.top.hom := by
  have h : HEq (((F).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (C) (D) (M))).map x y) ((L).map x y) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorAlgebraDiagonal_left]
  exact eq_of_heq h
lemma dgGluingMilnorAlgebraDiagonal_map_right (x y : P) :
    (F).map x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R (C) (D) (M) (X) (X) = d.side.hom := by
  have h : HEq (((F).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (C) (D) (M))).map x y) ((G).map x y) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorAlgebraDiagonal_right]
  have hh := eq_of_heq h
  change (F).map x y ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (C) (D) (M)).map (X) (X) = _ at hh
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map] at hh
  exact hh
lemma dgGluingMilnorAlgebraDiagonal_map_comparison (x y : P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison R (C) (D) (M) (X) (X) d.source.X ((F).map x y) = 0 := by
  let μ := dgHomGluingComparisonCycle R (C) (D) (E) (p) (q) (L) (G) (fun _ => 𝟙 _)
  let hn := dgHomGluingComparison_naturality R (C) (D) (E) (p) (q) (L) (G)
    (fun _ => 𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorAlgebraDiagonal_naturality R d)
  let A := dgStrictGluingCommaFamily R (C) (D) (M) (L) (G) μ hn
  have hm : (F).map x y ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R (C) (D) (M) (X) (X)).hom =
      A.toDGFunctor.map x y := by
    have h : HEq (((dgStrictGluingFunctor R (C) (D) (M) (L) (G) μ hn).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R (C) (D) (M))).map x y) (A.toDGFunctor.map x y) := by
      rw [dgStrictGluingFunctor_toComma]
    exact eq_of_heq h
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison_yoneda R (C) (D) (M) (X) (X) d.source.X ((F).map x y)
  rw [hm] at h
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R (D) (RightModule R (C)) (M).toFunctor
    (A.obj x) (A.obj y) d.source.X (A.homMap x y)).comp _ _ = _ at h
  erw [A.homMap_comparison x y, Cochain.zero_comp] at h
  exact h.symm
lemma dgGluingMilnorAlgebraDiagonal_map (x y : P) :
    (F).map x y = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison R d := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHom_ext R (C) (D) (M) (X) (X) d.source.X
  · exact (dgGluingMilnorAlgebraDiagonal_map_left R d x y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison_left R d).symm
  · exact (dgGluingMilnorAlgebraDiagonal_map_right R d x y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison_right R d).symm
  · exact (dgGluingMilnorAlgebraDiagonal_map_comparison R d x y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison_primitive R d).symm
lemma dgGluingMilnorAlgebraDiagonal_homQuasiIso (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    HomQuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorAlgebraDiagonal R d) := by
  intro x y
  rw [dgGluingMilnorAlgebraDiagonal_map]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison_quasiIso R d h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
