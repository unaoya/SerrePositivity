module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredCochains
public import SerrePositivity.AlgebraicGeometry.ModuleCatFilteredExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：増大を含む同じ全タプル Čech 微分と filtered 余極限の標準比較。
方針：既存の各項の関手と、既存の微分の自然性を使う。
規約：長さ0を含め、元の微分を変えない。
使われ方：アフィン被覆の増大完全性を実際の Frobenius 係数へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]

/-- 長さ0を含む元の全タプル Čech 微分は、係数図式に関する自然変換。 -/
def fullCechDifferentialNatTrans (k : ℕ) :
    projectiveCechCochainsFunctor (R := R) (ι := ι) k ⟶
      projectiveCechCochainsFunctor (k + 1) where
  app D := ModuleCat.ofHom (fullCechDifferential D k)
  naturality {D E} η := by
    apply ModuleCat.hom_ext
    exact (fullCechCochainsMap_comp_differential η k).symm

variable [Fintype ι] {J : Type u} [SmallCategory J] [IsFiltered J]
variable (D : J ⥤ Finset ι ⥤ ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
/-- 各項の標準余極限比較は、増大項から始まる同じ Čech 微分と可換。 -/
theorem fullCechFilteredDifferential_compare (k : ℕ) :
    colim.map (Functor.whiskerLeft D (fullCechDifferentialNatTrans k)) ≫
        (preservesColimitIso (projectiveCechCochainsFunctor (k + 1)) D).inv =
      (preservesColimitIso (projectiveCechCochainsFunctor k) D).inv ≫
        ModuleCat.ofHom (fullCechDifferential (colimit D) k) := by
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_map_assoc, ι_preservesColimitIso_inv]
  rw [ι_preservesColimitIso_inv_assoc]
  exact ((fullCechDifferentialNatTrans (R := R) (ι := ι) k).naturality
    (colimit.ι D j)).symm

end SerrePositivity.AlgebraicGeometry
