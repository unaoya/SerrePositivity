module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredSubmodule
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationMaps
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
概要：共通係数へ制限した次数付き加群図式の余極限の次数成分を作る。
方針：係数制限と余極限の比較を介し、各段の次数成分の像の有向上限を使う。
規約：多項式作用に使う環 P と次数成分の基底環 R を分ける。
使われ方：動く基底の模型の標準開と filtered 余極限の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} P)
local instance gradedColimitStageBaseModule (j : J) : Module R (M.obj j) :=
  Module.compHom (M.obj j) (algebraMap R P)
local instance gradedColimitStageBaseTower (j : J) : IsScalarTower R P (M.obj j) :=
  IsScalarTower.of_compHom R P (M.obj j)
local instance gradedColimitTargetBaseModule : Module R (colimit M : ModuleCat.{u} P) :=
  Module.compHom (colimit M : ModuleCat.{u} P) (algebraMap R P)
local instance gradedColimitTargetBaseTower :
    IsScalarTower R P (colimit M : ModuleCat.{u} P) :=
  IsScalarTower.of_compHom R P (colimit M : ModuleCat.{u} P)

variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (hG : ∀ {i j} (f : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map f).hom m ∈ G j n)

/-- 余極限の次数成分。共通基底での部分加群の余極限の像を使う。 -/
def projectiveGradedColimitGrade (n : ℕ) :
    Submodule R (colimit M : ModuleCat.{u} P) :=
  (projectiveFilteredSubmodule (M ⋙ ModuleCat.restrictScalars (algebraMap R P))
    (fun j ↦ G j n)).map
      (preservesColimitIso (ModuleCat.restrictScalars (algebraMap R P)) M).inv.hom

/-- 各段からの次数付き射の、基底上の線形写像。 -/
def projectiveGradedColimitBaseInclusion (j : J) :
    M.obj j →ₗ[R] (colimit M : ModuleCat.{u} P) :=
  ((ModuleCat.restrictScalars (algebraMap R P)).map (colimit.ι M j)).hom

include hG

/-- 余極限の次数成分の元は、一つの有限段の同じ次数の元で表される。 -/
theorem mem_projectiveGradedColimitGrade_iff (n : ℕ)
    (x : (colimit M : ModuleCat.{u} P)) :
    x ∈ projectiveGradedColimitGrade M G n ↔
      ∃ (j : J) (m : M.obj j), m ∈ G j n ∧ (colimit.ι M j).hom m = x := by
  have hi (j : J) (m : M.obj j) :
      (preservesColimitIso (ModuleCat.restrictScalars (algebraMap R P)) M).inv.hom
          ((colimit.ι (M ⋙ ModuleCat.restrictScalars (algebraMap R P)) j).hom m) =
        (colimit.ι M j).hom m :=
    congrArg (fun f ↦ f.hom m)
      (ι_preservesColimitIso_inv (ModuleCat.restrictScalars (algebraMap R P)) M j)
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨j, m, hm, he⟩ := (mem_projectiveFilteredSubmodule_iff
      (M ⋙ ModuleCat.restrictScalars (algebraMap R P)) (fun j ↦ G j n)
      (fun f m hm ↦ hG f n m hm) y).mp hy
    refine ⟨j, m, hm, ?_⟩
    exact (hi j m).symm.trans (congrArg _ he)
  · rintro ⟨j, m, hm, rfl⟩
    refine ⟨(colimit.ι (M ⋙ ModuleCat.restrictScalars (algebraMap R P)) j).hom m, ?_, hi j m⟩
    exact (mem_projectiveFilteredSubmodule_iff
      (M ⋙ ModuleCat.restrictScalars (algebraMap R P)) (fun j ↦ G j n)
      (fun f m hm ↦ hG f n m hm) _).mpr ⟨j, m, hm, rfl⟩

/-- 各有限段からの射は、同じ Proj 次数の成分を保つ。 -/
theorem projectiveGradedColimitInclusion_preservesPiece (j : J) (n : ℕ)
    (m : M.obj j) (hm : m ∈ G j n) :
    (colimit.ι M j).hom m ∈ projectiveGradedColimitGrade M G n :=
  (mem_projectiveGradedColimitGrade_iff M G hG n _).mpr ⟨j, m, hm, rfl⟩

/-- 有限段での分母倍の条件は、余極限の次数成分でも成り立つ。 -/
theorem projectiveGradedColimitGrade_step (f : P)
    (hstep : ∀ j n (m : G j n), f • m.val ∈ G j (n + 1))
    (n : ℕ) (x : projectiveGradedColimitGrade M G n) :
    f • x.val ∈ projectiveGradedColimitGrade M G (n + 1) := by
  obtain ⟨j, m, hm, he⟩ := (mem_projectiveGradedColimitGrade_iff M G hG n x.val).mp x.property
  apply (mem_projectiveGradedColimitGrade_iff M G hG (n + 1) _).mpr
  exact ⟨j, f • m, hstep j n ⟨m, hm⟩, by rw [map_smul, he]⟩

end SerrePositivity.AlgebraicGeometry
