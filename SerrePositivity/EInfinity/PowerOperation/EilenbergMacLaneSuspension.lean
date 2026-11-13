module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneCircle
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaSmashNaturality
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone

/-!
# Γ の指定された suspension 構造射

DAG XIII §2.2 のスペクトル忘却の前段。固定した基本円・AW の評価・左シフトの
符号なし比較を合成する。この定義だけでは Ω 条件を主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- シフトした単位とのテンソルは、左シフトした同じ複体である。 -/
def unitShiftTensorIso (M : Complex A) :
    (𝟙_ (Complex A))⟦(1 : ℤ)⟧ ⊗ M ≅ M⟦(1 : ℤ)⟧ :=
  SerrePositivity.cochainTensorShiftLeft (𝟙_ (Complex A)) M 1 ≪≫
    (shiftFunctor (Complex A) (1 : ℤ)).mapIso (λ_ M)

/-- 同じ Γ の suspension 射。基本円以外には代表の選択を行わない。 -/
def gammaSuspension (M : Complex A) :
    PointedObject.smash PointedSimplicialSet.circle.{u} (gammaPointed A M) ⟶
      gammaPointed A (M⟦(1 : ℤ)⟧) :=
  PointedObject.smashMap (unitCircle A) (𝟙 _) ≫
    gammaSmashPair A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) M ≫
      (gammaPointedFunctor A).map (unitShiftTensorIso A M).hom

/-- r 段から r+1 段への、添字の加法も指定した構造射。 -/
def levelSigma (M : Complex A) (r : ℕ) :
    PointedObject.smash PointedSimplicialSet.circle.{u}
      ((levelPointedFunctor A r).obj M) ⟶ (levelPointedFunctor A (r + 1)).obj M :=
  gammaSuspension A (M⟦(r : ℤ)⟧) ≫
    (gammaPointedFunctor A).map
      ((shiftFunctorAdd' (Complex A) (r : ℤ) 1 ((r + 1 : ℕ) : ℤ)
        (by omega)).inv.app M)

end SerrePositivity.EInfinity.PowerOperation
