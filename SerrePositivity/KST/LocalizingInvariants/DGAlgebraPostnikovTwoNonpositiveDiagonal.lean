module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoDiagonalPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackLowerBound
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverLiftNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverTowers

/-!
概要：二切断対角の非正次数模型を、元の二脚・対角と下界 −2 を保って構成する。
方針：元の対角を cover へ自然に持ち上げ、元の実 cocone 比較の pro 同型を反映する。
規約：正次数の消滅を元の経路模型へ仮定しない。使われ方：対角への二切断右逆構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

abbrev postnikovTwoDiagonalSource := postnikovUpperNonpositiveTower R (B := A) 2

abbrev postnikovTwoDiagonalRawTarget := modelTower R
  (f.map (postnikovFunctor R 2)) (f.map (postnikovFunctor R 2))

abbrev postnikovTwoDiagonalTarget :=
  (postnikovTwoDiagonalRawTarget R f).map (connectiveCoverNonpositive R)

def postnikovTwoNonpositiveDiagonal :
    LevelHom (postnikovTwoDiagonalSource R (A := A)) (postnikovTwoDiagonalTarget R f) where
  app i := ObjectProperty.homMk (connectiveCoverLift R
    (diagonal R (postnikovMap R (f.app i).hom 2)))
  naturality h := by
    apply ObjectProperty.hom_ext
    exact connectiveCoverLift_naturality R
      (diagonal R (postnikovMap R (f.app _).hom 2))
      (diagonal R (postnikovMap R (f.app _).hom 2))
      (postnikovMap R (A.transition h).hom 2)
      ((postnikovTwoDiagonalRawTarget R f).transition h)
      ((postnikovTwoRawDiagonal R f).naturality h)

lemma postnikovTwoNonpositiveDiagonal_inclusion (i : ℕ) :
    ((postnikovTwoNonpositiveDiagonal R f).app i).hom ≫
      connectiveCoverInclusion R ((postnikovTwoDiagonalRawTarget R f).obj i) =
        diagonal R (postnikovMap R (f.app i).hom 2) :=
  connectiveCoverLift_inclusion R _

def postnikovTwoDiagonalLeft (i : ℕ) : ((postnikovTwoDiagonalTarget R f).obj i).obj ⟶
    ((postnikovTwoDiagonalSource R (A := A)).obj i).obj :=
  connectiveCoverInclusion R ((postnikovTwoDiagonalRawTarget R f).obj i) ≫
    left R (postnikovMap R (f.app i).hom 2) (postnikovMap R (f.app i).hom 2)

def postnikovTwoDiagonalRight (i : ℕ) : ((postnikovTwoDiagonalTarget R f).obj i).obj ⟶
    ((postnikovTwoDiagonalSource R (A := A)).obj i).obj :=
  connectiveCoverInclusion R ((postnikovTwoDiagonalRawTarget R f).obj i) ≫
    right R (postnikovMap R (f.app i).hom 2) (postnikovMap R (f.app i).hom 2)

lemma postnikovTwoNonpositiveDiagonal_left (i : ℕ) :
    ((postnikovTwoNonpositiveDiagonal R f).app i).hom ≫ postnikovTwoDiagonalLeft R f i = 𝟙 _ := by
  rw [postnikovTwoDiagonalLeft, ← Category.assoc, postnikovTwoNonpositiveDiagonal_inclusion,
    diagonal_left]

lemma postnikovTwoNonpositiveDiagonal_right (i : ℕ) :
    ((postnikovTwoNonpositiveDiagonal R f).app i).hom ≫ postnikovTwoDiagonalRight R f i = 𝟙 _ := by
  rw [postnikovTwoDiagonalRight, ← Category.assoc, postnikovTwoNonpositiveDiagonal_inclusion,
    diagonal_right]

lemma postnikovTwoDiagonalRawTarget_lowerBound (i : ℕ) :
    ((postnikovTwoDiagonalRawTarget R f).obj i).X.IsStrictlyGE (-2) := by
  have : (postnikov R (A.obj i).obj 2).X.IsStrictlyGE (-2) := postnikov_lowerBound R _ 2
  have : (postnikov R (B.obj i).obj 2).X.IsStrictlyGE (-2) := postnikov_lowerBound R _ 2
  change (algebra R (postnikovMap R (f.app i).hom 2)
    (postnikovMap R (f.app i).hom 2)).X.IsStrictlyGE (-2)
  exact HomotopyPullbackModel.lowerBound R _ _ (-2)

lemma postnikovTwoDiagonalTarget_lowerBound (i : ℕ) :
    ((postnikovTwoDiagonalTarget R f).obj i).obj.X.IsStrictlyGE (-2) := by
  have := postnikovTwoDiagonalRawTarget_lowerBound R f i
  exact connectiveCover_lowerBound R _ (-2)

lemma postnikovTwoNonpositiveDiagonal_groups_proIso
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1)))
    (h₂ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2)))
    (j : ℤ) (hj : 0 ≤ j) (hj₂ : j ≤ 2) :
    IsProIso (((postnikovTwoNonpositiveDiagonal R f).map (nonpositiveInclusion R)).map
      (groups R j)) := by
  let a := ((postnikovTwoNonpositiveDiagonal R f).map (nonpositiveInclusion R)).map (groups R j)
  let b := (coverTowerCounit R (postnikovTwoDiagonalRawTarget R f)).map (groups R j)
  have : ∀ i, IsIso (b.app i) := fun i => connectiveCoverInclusion_groups_isIso R _ j hj
  apply TowerDiagram.proIso_of_comp_right_levelwiseIso b a
  have he : a.comp b = (postnikovTwoRawDiagonal R f).map (groups R j) := by
    apply ProSpectrum.levelHom_ext
    intro i
    exact ((groups R j).map_comp _ _).symm.trans
      (congrArg ((groups R j).map) (postnikovTwoNonpositiveDiagonal_inclusion R f i))
  rw [he]
  exact postnikovTwoRawDiagonal_groups_proIso R f h₀ h₁ h₂ j hj hj₂

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
