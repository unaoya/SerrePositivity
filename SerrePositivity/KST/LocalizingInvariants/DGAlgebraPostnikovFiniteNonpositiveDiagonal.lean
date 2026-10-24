module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteDiagonalPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackLowerBound
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverLiftNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverTowers

/-!
概要：有限切断対角の非正次数模型を、元の二脚・対角と下界 −n を保って構成する。
方針：元の対角を cover へ自然に持ち上げ、元の実 cocone 比較の pro 同型を反映する。
規約：正次数の消滅を元の経路模型へ仮定しない。使われ方：対角への有限切断右逆構成。
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
variable (R : Type u) [CommRing R] (n : ℤ) {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

abbrev postnikovFiniteDiagonalSource := postnikovUpperNonpositiveTower R (B := A) n

abbrev postnikovFiniteDiagonalRawTarget := modelTower R
  (f.map (postnikovFunctor R n)) (f.map (postnikovFunctor R n))

abbrev postnikovFiniteDiagonalTarget :=
  (postnikovFiniteDiagonalRawTarget R n f).map (connectiveCoverNonpositive R)

def postnikovFiniteNonpositiveDiagonal :
    LevelHom (postnikovFiniteDiagonalSource R n (A := A)) (postnikovFiniteDiagonalTarget R n f) where
  app i := ObjectProperty.homMk (connectiveCoverLift R
    (diagonal R (postnikovMap R (f.app i).hom n)))
  naturality h := by
    apply ObjectProperty.hom_ext
    exact connectiveCoverLift_naturality R
      (diagonal R (postnikovMap R (f.app _).hom n))
      (diagonal R (postnikovMap R (f.app _).hom n))
      (postnikovMap R (A.transition h).hom n)
      ((postnikovFiniteDiagonalRawTarget R n f).transition h)
      ((postnikovFiniteRawDiagonal R n f).naturality h)

lemma postnikovFiniteNonpositiveDiagonal_inclusion (i : ℕ) :
    ((postnikovFiniteNonpositiveDiagonal R n f).app i).hom ≫
      connectiveCoverInclusion R ((postnikovFiniteDiagonalRawTarget R n f).obj i) =
        diagonal R (postnikovMap R (f.app i).hom n) :=
  connectiveCoverLift_inclusion R _

def postnikovFiniteDiagonalLeft (i : ℕ) : ((postnikovFiniteDiagonalTarget R n f).obj i).obj ⟶
    ((postnikovFiniteDiagonalSource R n (A := A)).obj i).obj :=
  connectiveCoverInclusion R ((postnikovFiniteDiagonalRawTarget R n f).obj i) ≫
    left R (postnikovMap R (f.app i).hom n) (postnikovMap R (f.app i).hom n)

def postnikovFiniteDiagonalRight (i : ℕ) : ((postnikovFiniteDiagonalTarget R n f).obj i).obj ⟶
    ((postnikovFiniteDiagonalSource R n (A := A)).obj i).obj :=
  connectiveCoverInclusion R ((postnikovFiniteDiagonalRawTarget R n f).obj i) ≫
    right R (postnikovMap R (f.app i).hom n) (postnikovMap R (f.app i).hom n)

lemma postnikovFiniteNonpositiveDiagonal_left (i : ℕ) :
    ((postnikovFiniteNonpositiveDiagonal R n f).app i).hom ≫ postnikovFiniteDiagonalLeft R n f i = 𝟙 _ := by
  rw [postnikovFiniteDiagonalLeft, ← Category.assoc, postnikovFiniteNonpositiveDiagonal_inclusion,
    diagonal_left]

lemma postnikovFiniteNonpositiveDiagonal_right (i : ℕ) :
    ((postnikovFiniteNonpositiveDiagonal R n f).app i).hom ≫ postnikovFiniteDiagonalRight R n f i = 𝟙 _ := by
  rw [postnikovFiniteDiagonalRight, ← Category.assoc, postnikovFiniteNonpositiveDiagonal_inclusion,
    diagonal_right]

lemma postnikovFiniteDiagonalRawTarget_lowerBound (i : ℕ) :
    ((postnikovFiniteDiagonalRawTarget R n f).obj i).X.IsStrictlyGE (-n) := by
  have : (postnikov R (A.obj i).obj n).X.IsStrictlyGE (-n) := postnikov_lowerBound R _ n
  have : (postnikov R (B.obj i).obj n).X.IsStrictlyGE (-n) := postnikov_lowerBound R _ n
  change (algebra R (postnikovMap R (f.app i).hom n)
    (postnikovMap R (f.app i).hom n)).X.IsStrictlyGE (-n)
  exact HomotopyPullbackModel.lowerBound R _ _ (-n)

lemma postnikovFiniteDiagonalTarget_lowerBound (i : ℕ) :
    ((postnikovFiniteDiagonalTarget R n f).obj i).obj.X.IsStrictlyGE (-n) := by
  have := postnikovFiniteDiagonalRawTarget_lowerBound R n f i
  exact connectiveCover_lowerBound R _ (-n)

lemma postnikovFiniteNonpositiveDiagonal_groups_proIso
    (h : ∀ j : ℤ, 0 ≤ j → j ≤ n →
      IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j)))
    (j : ℤ) (hj : 0 ≤ j) (hjn : j ≤ n) :
    IsProIso (((postnikovFiniteNonpositiveDiagonal R n f).map (nonpositiveInclusion R)).map
      (groups R j)) := by
  let a := ((postnikovFiniteNonpositiveDiagonal R n f).map (nonpositiveInclusion R)).map (groups R j)
  let b := (coverTowerCounit R (postnikovFiniteDiagonalRawTarget R n f)).map (groups R j)
  have : ∀ i, IsIso (b.app i) := fun i => connectiveCoverInclusion_groups_isIso R _ j hj
  apply TowerDiagram.proIso_of_comp_right_levelwiseIso b a
  have he : a.comp b = (postnikovFiniteRawDiagonal R n f).map (groups R j) := by
    apply ProSpectrum.levelHom_ext
    intro i
    exact ((groups R j).map_comp _ _).symm.trans
      (congrArg ((groups R j).map) (postnikovFiniteNonpositiveDiagonal_inclusion R n f i))
  rw [he]
  exact postnikovFiniteRawDiagonal_groups_proIso R n f h j hj hjn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
