module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSuspension
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift

/-!
# Γ の suspension 構造射の自然性

DAG XIII §2.2 のスペクトル忘却の前段。固定基本円を変えず、複体の任意の射で可換する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma unitShiftTensorIso_naturality {M N : Complex A} (f : M ⟶ N) :
    (𝟙 ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) ⊗ₘ f) ≫ (unitShiftTensorIso A N).hom =
      (unitShiftTensorIso A M).hom ≫ f⟦(1 : ℤ)⟧' := by
  dsimp only [unitShiftTensorIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, tensorShiftLeft_second_naturality, Category.assoc,
    ← Functor.map_comp, Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg ((shiftFunctor (Complex A) (1 : ℤ)).map)
  simpa only [id_tensorHom] using leftUnitor_naturality f

set_option maxHeartbeats 800000 in
-- Γ の smash 商と元の複体の同じ対象の照合に必要な定義展開を検査する。
lemma gammaSuspension_naturality {M N : Complex A} (f : M ⟶ N) :
    PointedObject.smashMap (𝟙 PointedSimplicialSet.circle.{u})
      ((gammaPointedFunctor A).map f) ≫ gammaSuspension A N =
    gammaSuspension A M ≫ (gammaPointedFunctor A).map (f⟦(1 : ℤ)⟧') := by
  dsimp only [gammaSuspension]
  rw [← Category.assoc, PointedObject.smashMap_comp]
  erw [Category.id_comp, Category.comp_id]
  rw [show PointedObject.smashMap (unitCircle A) ((gammaPointedFunctor A).map f) =
    PointedObject.smashMap (unitCircle A) (𝟙 _) ≫
      PointedObject.smashMap (𝟙 _) ((gammaPointedFunctor A).map f) by
        rw [PointedObject.smashMap_comp]; simp]
  rw [Category.assoc]
  have h := gammaSmashPair_naturality A (𝟙 ((𝟙_ (Complex A))⟦(1 : ℤ)⟧)) f
  simp only [(gammaPointedFunctor A).map_id] at h
  slice_lhs 2 3 => exact h
  simp only [Category.assoc]
  rw [
    ← Functor.map_comp,
    unitShiftTensorIso_naturality, Functor.map_comp]
  rfl

end SerrePositivity.EInfinity.PowerOperation
