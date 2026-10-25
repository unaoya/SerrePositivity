module
public import SerrePositivity.DifferentialGraded.Presentation.CategoryData
public import SerrePositivity.DifferentialGraded.Presentation.ZeroComplexCode
public import SerrePositivity.DifferentialGraded.Presentation.EnrichedLawTransport
/-!
概要：固定基底を共有する dg 圏提示データの非連結和を構成する。
方針：同じ成分の Hom を保ち、異なる成分の Hom は零提示にする。
規約：対象集合の ordinal への再添字と seed の延長は別に行う。
使われ方：二項・可算個の出発提示の同時精密化の対象側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (R : Type u) [CommRing R] (B J : Type u) (X : J → Type u)
  (c : ∀ j, DGCategoryPresentationData R B (X j))
local instance : DecidableEq J := Classical.decEq J

namespace DGCategoryPresentationData

def sigmaHom (x y : Sigma X) : DGComplexPresentationCode R B :=
  if h : x.1 = y.1 then (c x.1).hom x.2 (h.symm ▸ y.2) else DGComplexPresentationCode.zero R B

lemma sigmaHom_same (j : J) (x y : X j) :
    sigmaHom R B J X c ⟨j, x⟩ ⟨j, y⟩ = (c j).hom x y := by simp [sigmaHom]

lemma sigmaHom_value_same (j : J) (x y : X j) :
    (sigmaHom R B J X c ⟨j, x⟩ ⟨j, y⟩).value R B = ((c j).hom x y).value R B :=
  congrArg (DGComplexPresentationCode.value R B) (sigmaHom_same R B J X c j x y)

lemma sigmaHom_isZero_ne {j k : J} (h : j ≠ k) (x : X j) (y : X k) :
    IsZero ((sigmaHom R B J X c ⟨j, x⟩ ⟨k, y⟩).value R B) := by
  simpa [sigmaHom, h] using DGComplexPresentationCode.zero_value_isZero R B

def sigmaUnit (x : Sigma X) : 𝟙_ (Complex R) ⟶ (sigmaHom R B J X c x x).value R B := by
  rcases x with ⟨j, x⟩
  exact cast (congrArg (fun h : DGComplexPresentationCode R B =>
    𝟙_ (Complex R) ⟶ h.value R B) (sigmaHom_same R B J X c j x x).symm) ((c j).unit x)

def sigmaComp (x y z : Sigma X) :
    (sigmaHom R B J X c x y).value R B ⊗ (sigmaHom R B J X c y z).value R B ⟶
      (sigmaHom R B J X c x z).value R B := by
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  rcases z with ⟨l, z⟩
  by_cases h : j = k
  · subst k
    by_cases h' : j = l
    · subst l
      exact cast (by simp only [sigmaHom_same]) ((c j).comp x y z)
    · exact 0
  · exact 0

lemma sigmaUnit_heq (j : J) (x : X j) :
    HEq (sigmaUnit R B J X c ⟨j, x⟩) ((c j).unit x) := by
  dsimp only [sigmaUnit]
  exact cast_heq _ _

lemma sigmaComp_heq (j : J) (x y z : X j) :
    HEq (sigmaComp R B J X c ⟨j, x⟩ ⟨j, y⟩ ⟨j, z⟩) ((c j).comp x y z) := by
  dsimp only [sigmaComp]
  split_ifs <;> first | exact cast_heq _ _ | contradiction

lemma sigmaLeft (x y : Sigma X) :
    (λ_ ((sigmaHom R B J X c x y).value R B)).inv ≫
      sigmaUnit R B J X c x ▷ _ ≫ sigmaComp R B J X c x x y = 𝟙 _ := by
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  by_cases h : j = k
  · subst k
    exact enrichedLeftLaw_of_heq
      (sigmaHom_value_same R B J X c j x x) (sigmaHom_value_same R B J X c j x y)
      _ _ _ _ (sigmaUnit_heq R B J X c j x) (sigmaComp_heq R B J X c j x x y)
      ((c j).left x y)
  · exact (sigmaHom_isZero_ne R B J X c h x y).eq_of_tgt _ _

lemma sigmaRight (x y : Sigma X) :
    (ρ_ ((sigmaHom R B J X c x y).value R B)).inv ≫
      _ ◁ sigmaUnit R B J X c y ≫ sigmaComp R B J X c x y y = 𝟙 _ := by
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  by_cases h : j = k
  · subst k
    exact enrichedRightLaw_of_heq
      (sigmaHom_value_same R B J X c j y y) (sigmaHom_value_same R B J X c j x y)
      _ _ _ _ (sigmaUnit_heq R B J X c j y) (sigmaComp_heq R B J X c j x y y)
      ((c j).right x y)
  · exact (sigmaHom_isZero_ne R B J X c h x y).eq_of_tgt _ _

lemma sigmaAssoc (w x y z : Sigma X) :
    (α_ _ _ _).inv ≫ sigmaComp R B J X c w x y ▷ _ ≫ sigmaComp R B J X c w y z =
      _ ◁ sigmaComp R B J X c x y z ≫ sigmaComp R B J X c w x z := by
  rcases w with ⟨i, w⟩
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  rcases z with ⟨l, z⟩
  by_cases h₁ : i = j
  · subst j
    by_cases h₂ : i = k
    · subst k
      by_cases h₃ : i = l
      · subst l
        exact enrichedAssocLaw_of_heq
          (sigmaHom_value_same R B J X c i w x) (sigmaHom_value_same R B J X c i x y)
          (sigmaHom_value_same R B J X c i y z) (sigmaHom_value_same R B J X c i w y)
          (sigmaHom_value_same R B J X c i x z) (sigmaHom_value_same R B J X c i w z)
          _ _ _ _ _ _ _ _ (sigmaComp_heq R B J X c i w x y)
          (sigmaComp_heq R B J X c i w y z) (sigmaComp_heq R B J X c i x y z)
          (sigmaComp_heq R B J X c i w x z) ((c i).assoc w x y z)
      · exact ((tensorLeft ((sigmaHom R B J X c ⟨i, w⟩ ⟨i, x⟩).value R B)).map_isZero
          ((tensorLeft ((sigmaHom R B J X c ⟨i, x⟩ ⟨i, y⟩).value R B)).map_isZero
            (sigmaHom_isZero_ne R B J X c h₃ y z))).eq_of_src _ _
    · exact ((tensorLeft ((sigmaHom R B J X c ⟨i, w⟩ ⟨i, x⟩).value R B)).map_isZero
        ((tensorRight ((sigmaHom R B J X c ⟨k, y⟩ ⟨l, z⟩).value R B)).map_isZero
          (sigmaHom_isZero_ne R B J X c h₂ x y))).eq_of_src _ _
  · exact ((tensorRight
      ((sigmaHom R B J X c ⟨j, x⟩ ⟨k, y⟩).value R B ⊗
        (sigmaHom R B J X c ⟨k, y⟩ ⟨l, z⟩).value R B)).map_isZero
        (sigmaHom_isZero_ne R B J X c h₁ w x)).eq_of_src _ _

def sigma : DGCategoryPresentationData R B (Sigma X) where
  hom := sigmaHom R B J X c
  unit := sigmaUnit R B J X c
  comp := sigmaComp R B J X c
  left := sigmaLeft R B J X c
  right := sigmaRight R B J X c
  assoc := sigmaAssoc R B J X c

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
