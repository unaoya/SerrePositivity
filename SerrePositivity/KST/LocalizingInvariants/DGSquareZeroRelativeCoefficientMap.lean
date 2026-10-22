module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportIso
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessCoefficient

/-!
概要：実係数射と厳密 class 可換式から、底を固定した相対拡大模型の射を作る。
方針：元の模型の経路を Path.map で移し、元の両脚とともに実普遍 lift に渡す。
規約：係数の準同型性を要求しない。使われ方：二切断候補の Γ の実模型射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A}
  (m : M ⟶ N) (a : W ⟶ SquareZero.algebra A M) (b : W ⟶ SquareZero.algebra A N)
  (h : a ≫ SquareZero.coefficientMap A m = b)

def coefficientWitness : DGAlgebra.Path.Witness R (relativeLeft M a ≫ b)
    (relativeRight M a ≫ SquareZero.zeroSection A N) where
  hom := relativePath M a ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A m)
  source_eq := by
    have hs : relativePath M a ≫ DGAlgebra.Path.source R (SquareZero.algebra A M) =
        relativeLeft M a ≫ a := (relativeWitness M a).source_eq
    rw [Category.assoc, DGAlgebra.Path.map_source, ← Category.assoc,
      hs, Category.assoc, h]
  target_eq := by
    have ht : relativePath M a ≫ DGAlgebra.Path.target R (SquareZero.algebra A M) =
        relativeRight M a ≫ SquareZero.zeroSection A M := (relativeWitness M a).target_eq
    rw [Category.assoc, DGAlgebra.Path.map_target, ← Category.assoc,
      ht, Category.assoc, SquareZero.zeroSection_coefficientMap]

def coefficientModelMap : relativeModel M a ⟶ relativeModel N b :=
  DGAlgebra.RelativeHomotopyPullback.lift R (SquareZero.projection A N) b
    (SquareZero.zeroSection A N) (relativeLeft M a) (relativeRight M a)
    (coefficientWitness m a b h) (by
      change (relativePath M a ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A m)) ≫
        DGAlgebra.Path.map R (SquareZero.projection A N) = _
      rw [Category.assoc, ← DGAlgebra.Path.map_comp, SquareZero.coefficientMap_projection,
        relativePath_base, ← h]
      simp only [Category.assoc, SquareZero.coefficientMap_projection])

lemma coefficientModelMap_left :
    coefficientModelMap m a b h ≫ relativeLeft N b = relativeLeft M a :=
  DGAlgebra.RelativeHomotopyPullback.lift_left R _ _ _ _ _ _ _

lemma coefficientModelMap_right :
    coefficientModelMap m a b h ≫ relativeRight N b = relativeRight M a :=
  DGAlgebra.RelativeHomotopyPullback.lift_right R _ _ _ _ _ _ _

lemma coefficientModelMap_path : coefficientModelMap m a b h ≫ relativePath N b =
    relativePath M a ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A m) :=
  DGAlgebra.RelativeHomotopyPullback.lift_path R _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
