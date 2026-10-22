module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNormalizedClassPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCospanProComparison

/-!
概要：n=1 の元の源射の class 模型は、準同型を反転する圏で実 pro 同型となる。
方針：元の左準同型・中心 pro 逆・右同型を、実 cospan 分解と経路模型へ渡す。
規約：同じ class 模型と元の射を保持。使われ方：有限一切断の実逆 roof。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma postnikovNormalizedClassModelMap_isProIso (hL : InvertsQuasiIsos R L)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso (((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovClassModelFunctor R 0 (by omega))).map L) := by
  apply HomotopyPullbackModel.diagramMap_isProIso_of_inverts R
    ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovClassCospanFunctor R 0 (by omega))) L hL
  · exact postnikovNormalizedPerturbedMap_quasiIso R f
  · exact postnikovNormalizedDerivationTargetMap_isProIso R f hf
  · change IsProIso ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovFunctor R 0))
    have : ∀ i, IsIso (((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
        (postnikovFunctor R 0)).app i) :=
      postnikovStrictZeroBaseLift_zeroMap_isIso R f 1 (by omega)
    exact TowerDiagram.isProIso_of_levelwiseIso _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
