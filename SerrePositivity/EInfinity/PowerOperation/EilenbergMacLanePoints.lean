module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLevels
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
# 各段の自然な零基点

DAG XIII §2.2 のスペクトル忘却への前段。
Γ の単体的加群の零元を全単体次数で保持し、全鎖写像を基点付き写像へ送る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 単体的加群の零元を自然な基点とする全関手。 -/
def modulePointedFunctor : SimplicialObject (ModuleCat A) ⥤ PointedSimplicialSet.{u} where
  obj W := Under.mk (show 𝟙_ SSet ⟶ W ⋙ forget (ModuleCat A) from {
    app Δ := ↾fun _ => 0
    naturality := by
      intro Δ Γ f
      ext x
      exact (map_zero (W.map f).hom).symm })
  map f := Under.homMk (Functor.whiskerRight f (forget (ModuleCat A))) (by
    ext Δ x
    exact map_zero (f.app Δ).hom)
  map_id W := by ext Δ x; rfl
  map_comp f g := by ext Δ x; rfl

/-- 同じ Γ の第 n 段に零基点を入れる全関手。 -/
def levelPointedFunctor (n : ℕ) : Complex A ⥤ PointedSimplicialSet.{u} :=
  levelModuleFunctor A n ⋙ modulePointedFunctor A

/-- 基点を忘れた全関手は、元の同じ段の関手である。 -/
lemma levelPointedFunctor_forget (n : ℕ) :
    levelPointedFunctor A n ⋙ PointedSimplicialSet.forget = levelSpaceFunctor A n := rfl

end SerrePositivity.EInfinity.PowerOperation
