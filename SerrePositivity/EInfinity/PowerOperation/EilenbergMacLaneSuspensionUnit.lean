module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSmashUnit
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSuspension

/-!
# 指定 suspension 射の単位上での計算

DAG XIII §2.2 の Ω 比較への前段。基本円の同じ代表を保持する。
右単位子と左シフト同型の比較は実際の自己同型として明示し、恒等射とは仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma gammaSmashPair_unit_postcomp {K L : Complex A} (f : K ⊗ 𝟙_ (Complex A) ⟶ L) :
    (gammaPointed A K ◁ gammaUnitBasedPoint A) ≫ gammaSmashPair A K (𝟙_ (Complex A)) ≫
      (gammaPointedFunctor A).map f =
    (ρ_ (gammaPointed A K)).hom ≫ (gammaPointedFunctor A).map ((ρ_ K).inv ≫ f) := by
  calc
    _ = (gammaPointed A K ◁ gammaUnitBasedPoint A) ≫
        gammaSmashPair A K (𝟙_ (Complex A)) ≫
          (gammaPointedFunctor A).map (ρ_ K).hom ≫
            (gammaPointedFunctor A).map ((ρ_ K).inv ≫ f) := by
      rw [← Functor.map_comp, Iso.hom_inv_id_assoc]
    _ = _ := by
      slice_lhs 1 3 => exact gammaSmashPair_right_unit A K

/-- 二つの指定単位比較の差を、シフトした単位の実際の自己同型として保持する。 -/
def unitShiftAutomorphism : (𝟙_ (Complex A))⟦(1 : ℤ)⟧ ≅
    (𝟙_ (Complex A))⟦(1 : ℤ)⟧ :=
  (ρ_ ((𝟙_ (Complex A))⟦(1 : ℤ)⟧)).symm ≪≫ unitShiftTensorIso A (𝟙_ (Complex A))

/-- suspension 射の単位上の値は、固定した基本円を指定自己同型で写した射である。 -/
lemma gammaSuspension_on_unit :
    (PointedSimplicialSet.circle.{u} ◁ gammaUnitBasedPoint A) ≫
      gammaSuspension A (𝟙_ (Complex A)) =
    (ρ_ PointedSimplicialSet.circle.{u}).hom ≫ unitCircle A ≫
      (gammaPointedFunctor A).map (unitShiftAutomorphism A).hom := by
  dsimp only [gammaSuspension]
  change PointedObject.smashMap (𝟙 PointedSimplicialSet.circle.{u})
    (gammaUnitBasedPoint A) ≫ PointedObject.smashMap (unitCircle A) (𝟙 _) ≫
      gammaSmashPair A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) (𝟙_ (Complex A)) ≫
        (gammaPointedFunctor A).map (unitShiftTensorIso A (𝟙_ (Complex A))).hom = _
  rw [← Category.assoc, PointedObject.smashMap_comp]
  erw [Category.id_comp, Category.comp_id]
  change (unitCircle A ⊗ₘ gammaUnitBasedPoint A) ≫
    gammaSmashPair A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) (𝟙_ (Complex A)) ≫ _ = _
  rw [tensorHom_def]
  simp only [Category.assoc]
  slice_lhs 2 4 =>
    exact gammaSmashPair_unit_postcomp A (unitShiftTensorIso A (𝟙_ (Complex A))).hom
  change (unitCircle A ▷ 𝟙_ PointedSimplicialSet.{u}) ≫
    (ρ_ (gammaPointed A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧))).hom ≫ _ = _
  rw [← Category.assoc, rightUnitor_naturality, Category.assoc]
  rfl

end SerrePositivity.EInfinity.PowerOperation
