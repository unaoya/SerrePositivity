module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayColimit

/-!
概要：斉次局所化の余極限比較を、周囲の局所化の値で計算する。
方針：部分加群の移送を消し、局所化写像だけの式を切り出す。
規約：次数成分の基底 R と作用の環 P は区別する。
使われ方：実際の標準開への比較で、余錐の定義の展開を局所化する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} P)
local instance gradedAwayColimitValuesBaseModule (V : ModuleCat.{u} P) : Module R V :=
  Module.compHom V (algebraMap R P)
local instance gradedAwayColimitValuesBaseTower (V : ModuleCat.{u} P) : IsScalarTower R P V :=
  IsScalarTower.of_compHom R P V
variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable (f : P) (hstep : ∀ j n (m : G j n), f • m.val ∈ G j (n + 1))

/-- 斉次局所化の余極限同型は、周囲の局所化では各有限段からの局所化写像。 -/
theorem projectiveGradedAwayColimitEquiv_ι_value (j : J)
    (z : projectiveGradedAway f (G j)) :
    (projectiveGradedAwayColimitEquiv M G hG f hstep
      ((colimit.ι (projectiveGradedAwayColimitDiagram M G hG f) j).hom z)).val =
      IsLocalizedModule.map (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (M.obj j))
        (LocalizedModule.mkLinearMap (Submonoid.powers f)
          (colimit M : ModuleCat.{u} P)) (colimit.ι M j).hom z.val := by
  rw [projectiveGradedAwayColimitEquiv_ι]
  rfl

end SerrePositivity.AlgebraicGeometry
