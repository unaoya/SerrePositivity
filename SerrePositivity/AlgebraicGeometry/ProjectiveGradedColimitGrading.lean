module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedColimit
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading

/-!
概要：余極限の次数成分と、整数への零延長・次数付き多項式作用を比較する。
方針：有限段の同じ次数の代表元を使い、負の次数は零として計算する。
規約：次数成分の基底 R と作用の環 P は区別する。
使われ方：斉次局所化の比較を実際の射影標準開へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} P)
local instance gradedColimitGradingStageBaseModule (j : J) : Module R (M.obj j) :=
  Module.compHom (M.obj j) (algebraMap R P)
local instance gradedColimitGradingStageBaseTower (j : J) : IsScalarTower R P (M.obj j) :=
  IsScalarTower.of_compHom R P (M.obj j)
local instance gradedColimitGradingTargetBaseModule : Module R (colimit M : ModuleCat.{u} P) :=
  Module.compHom (colimit M : ModuleCat.{u} P) (algebraMap R P)
local instance gradedColimitGradingTargetBaseTower :
    IsScalarTower R P (colimit M : ModuleCat.{u} P) :=
  IsScalarTower.of_compHom R P (colimit M : ModuleCat.{u} P)


/-- 各段の零部分の余極限の像は零部分。 -/
theorem projectiveGradedColimitGrade_bot (n : ℕ) :
    projectiveGradedColimitGrade (R := R) M (fun _ _ ↦ ⊥) n =
      (⊥ : Submodule R (colimit M : ModuleCat.{u} P)) := by
  simp [projectiveGradedColimitGrade, projectiveFilteredSubmodule]

variable (G : ∀ j, ℕ → Submodule R (M.obj j))

/-- 余極限の次数成分と、負の次数を零とする整数への延長は交換する。 -/
theorem projectiveGradedColimitGrade_int (e : ℕ → ℤ) (n : ℕ) :
    projectiveGradedColimitGrade M (fun j k ↦ projectiveNatGradingInt (G j) (e k)) n =
      projectiveNatGradingInt (projectiveGradedColimitGrade M G) (e n) := by
  by_cases h : 0 ≤ e n
  · simp only [projectiveGradedColimitGrade, projectiveFilteredSubmodule,
      projectiveNatGradingInt, h, ite_true]
  · simp [projectiveGradedColimitGrade, projectiveFilteredSubmodule,
      projectiveNatGradingInt, h]

variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable (B : ℕ → Submodule R P) [∀ j, SetLike.GradedSMul B (G j)]

/-- 有限段の次数付き作用を、余極限の実際の次数成分へ移す。 -/
@[instance_reducible] def projectiveGradedColimitGradeGradedSMul :
    SetLike.GradedSMul B (projectiveGradedColimitGrade M G) where
  smul_mem := by
    intro i j a x ha hx
    obtain ⟨k, m, hm, he⟩ := (mem_projectiveGradedColimitGrade_iff M G hG j x).mp hx
    apply (mem_projectiveGradedColimitGrade_iff M G hG (i + j) _).mpr
    exact ⟨k, a • m, SetLike.GradedSMul.smul_mem ha hm, by rw [map_smul, he]⟩

end SerrePositivity.AlgebraicGeometry
