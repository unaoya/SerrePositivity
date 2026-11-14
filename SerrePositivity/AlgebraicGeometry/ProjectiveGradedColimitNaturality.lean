module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedColimit

/-!
概要：次数成分の filtered colimit を、次数を保つ図式の射に自然にする。
方針：一つの有限段の同じ次数の代表元で比較する。
規約：次数成分の基底 R と作用の環 P は区別する。
使われ方：標準開・Čech の余極限比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M N : J ⥤ ModuleCat.{u} P)
local instance gradedColimitNaturalBaseModule (V : ModuleCat.{u} P) : Module R V :=
  Module.compHom V (algebraMap R P)
local instance gradedColimitNaturalBaseTower (V : ModuleCat.{u} P) : IsScalarTower R P V :=
  IsScalarTower.of_compHom R P V
variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (H : ∀ j, ℕ → Submodule R (N.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable (hH : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : N.obj i),
  m ∈ H i n → (N.map α).hom m ∈ H j n)

include hG hH in
/-- 次数を保つ図式の射は、余極限の実際の次数成分も保つ。 -/
theorem projectiveGradedColimitMap_preservesPiece (η : M ⟶ N)
    (hη : ∀ j n (m : M.obj j), m ∈ G j n → (η.app j).hom m ∈ H j n)
    (n : ℕ) (x : (colimit M : ModuleCat.{u} P))
    (hx : x ∈ projectiveGradedColimitGrade M G n) :
    (colim.map η).hom x ∈ projectiveGradedColimitGrade N H n := by
  obtain ⟨j, m, hm, rfl⟩ := (mem_projectiveGradedColimitGrade_iff M G hG n x).mp hx
  apply (mem_projectiveGradedColimitGrade_iff N H hH n _).mpr
  refine ⟨j, (η.app j).hom m, hη j n m hm, ?_⟩
  exact (congrArg (fun f ↦ f.hom m) (colimit.ι_map η j)).symm

end SerrePositivity.AlgebraicGeometry
