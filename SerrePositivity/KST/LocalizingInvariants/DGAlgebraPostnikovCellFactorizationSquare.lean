module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationWitness
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportHomotopy

/-!
概要：同じ合成射の二因子分解の class 合成経路を、同じ共通底 P 上で実際に比較する。
方針：元の摂動射上の二経路を cell 充填し、同じ四重射影の底へ移す。
規約：二つの比較の相対模型は同じ。使われ方：Γ の右自然性の実経路比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (h : B ⟶ D)
  (C C' : Mon (Complex R)) [C.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)
  (f' : B ⟶ C') (g' : C' ⟶ D) (heq' : f' ≫ g' = h)

def postnikovCellFactorizationClassSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellFactorizationClassWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationClassWitness R B D P n hn b h C' f' g' heq') := by
  let z := SquareZero.cellClassWitnessSquare R (postnikovPerturbedProjection R D n hn)
    (postnikovPerturbedProjection_surjective R D n hn)
    (postnikovPerturbedProjection_quasiIso R D n hn)
    (postnikovCellLiftFactorizationWitness R B C D P n hn b h f g heq)
    (postnikovCellLiftFactorizationWitness R B C' D P n hn b h f' g' heq')
    (postnikovCellLiftFactorizationWitness_relative R B C D P n hn b h f g heq)
    (postnikovCellLiftFactorizationWitness_relative R B C' D P n hn b h f' g' heq')
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
    (postnikovPerturbedClass_projection R D n hn)
  refine {
    toWitness := z.toWitness
    source_trace := z.source_trace
    target_trace := z.target_trace
    projection_eq := ?_ }
  exact z.projection_eq.trans (congrArg (fun t =>
    (t ≫ Path.diagonal R (postnikov R D n)) ≫
      Path.diagonal R (Path.algebra R (postnikov R D n)))
    (postnikovCellFactorization_base R B D P n hn b h))

def postnikovCellFactorizationCommonSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellFactorizationCommonWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationCommonWitness R B D P n hn b h C' f' g' heq') :=
  SquareZero.baseChangeRelativeWitnessSquare (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
    (postnikovCellFactorizationClassSquare R B D P n hn b h C C' f g heq f' g' heq')

def postnikovCellFactorizationTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
      (postnikovCellFactorizationCommonWitness R B D P n hn b h C f g heq))
    (SquareZeroExtension.transport
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
      (postnikovCellFactorizationCommonWitness R B D P n hn b h C' f' g' heq')) :=
  SquareZeroExtension.transportHomotopy _
    (postnikovCellFactorizationCommonSquare R B D P n hn b h C C' f g heq f' g' heq')

lemma postnikovCellFactorizationTransportHomotopy_left :
    (postnikovCellFactorizationTransportHomotopy R B D P n hn b h C C'
      f g heq f' g' heq').hom ≫ Path.map R (SquareZeroExtension.relativeLeft
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
      (postnikovCellFactorizationCommonTarget R B D P n hn b h)) =
    SquareZeroExtension.relativeLeft
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
      (postnikovCellFactorizationCommonSource R B D P n hn b h) ≫
      Path.diagonal R (cellResolution R (cellResolution R
        (cellResolution R (cellResolution R P)))) :=
  SquareZeroExtension.transportHomotopy_left _
    (postnikovCellFactorizationCommonSquare R B D P n hn b h C C' f g heq f' g' heq')

lemma postnikovCellFactorizationTransportHomotopy_right :
    (postnikovCellFactorizationTransportHomotopy R B D P n hn b h C C'
      f g heq f' g' heq').hom ≫ Path.map R (SquareZeroExtension.relativeRight
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
      (postnikovCellFactorizationCommonTarget R B D P n hn b h)) =
    SquareZeroExtension.relativeRight
      (bimoduleRestrict (b ≫ postnikovMap R h n) (postnikovShiftedLayerBimodule R D n hn 1))
      (postnikovCellFactorizationCommonSource R B D P n hn b h) ≫ Path.diagonal R P :=
  SquareZeroExtension.transportHomotopy_right _
    (postnikovCellFactorizationCommonSquare R B D P n hn b h C C' f g heq f' g' heq')

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
