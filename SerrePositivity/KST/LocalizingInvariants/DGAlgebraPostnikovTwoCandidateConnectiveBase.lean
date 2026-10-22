module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCandidateBaseValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofCoverValueTransport

/-!
概要：元の実二切断候補の底の式を、connective 準同型だけを反転する関手へ移す。
方針：同じ cover 前合成で全準同型反転版を評価し、元の counit で実 roof の値へ戻す。
規約：模型全体や元の関手に全準同型反転を追加入力しない。使われ方：具体的不変量値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)
  (hL : InvertsConnectiveQuasiIsos R L)

lemma candidateRoof_connectiveValue_base :
    SurjectiveRoof.connectiveValue R L hL
      (postnikov_isConnective R (B.obj d.layerInverse.zero.stage).obj 2) (d.candidateRoof R) ≫
        L.map (postnikovTransition R (A.obj j).obj 2 1 (by omega)) =
    L.map (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj 2 1 (by omega)) ≫
      SurjectiveRoof.connectiveValue R L hL
        (postnikov_isConnective R (B.obj d.layerInverse.zero.stage).obj 1)
          (d.lowerBaseInverse R).roof :=
  SurjectiveRoof.connectiveValue_square_of_cover R L hL
    (postnikov_isConnective R (B.obj d.layerInverse.zero.stage).obj 2)
    (postnikov_isConnective R (B.obj d.layerInverse.zero.stage).obj 1)
    (d.candidateRoof R) (d.lowerBaseInverse R).roof
    (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj 2 1 (by omega))
    (postnikovTransition R (A.obj j).obj 2 1 (by omega))
    (d.candidateRoof_value_base R (connectiveCoverFunctor R ⋙ L)
      (invertsQuasiIsos_coverFunctor R L hL))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
