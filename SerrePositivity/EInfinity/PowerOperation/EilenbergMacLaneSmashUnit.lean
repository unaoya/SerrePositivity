module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaUnitPoint
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaSmashNaturality
public import SerrePositivity.EInfinity.PowerOperation.PointedSmashUnitSeed

/-!
# Γ の smash 積の指定右単位

DAG XIII §2.2 の基本円の照合への前段。零次球面の非基点を AW 単位へ送り、
零基点も保持したまま指定右単位子との一致を証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.PointedSimplicialSet
variable (A : Type u) [CommRing A]

/-- 零次球面の非基点を、元の AW 単位の全単体の点へ送る。 -/
def gammaUnitBasedPoint : 𝟙_ PointedSimplicialSet.{u} ⟶ gammaPointed A (𝟙_ (Complex A)) :=
  (PointedObject.adjoinHomEquiv (𝟙_ SSet.{u}) (gammaPointed A (𝟙_ (Complex A)))).symm
    (gammaUnitPoint A)

lemma gammaUnitBasedPoint_underlying :
    forgetUnit ≫ (gammaUnitBasedPoint A).right = gammaUnitPoint A := by
  rw [forgetUnit_comp]
  exact Equiv.apply_symm_apply _ _

/-- smash の商へ引き戻した射は、指定 Γ の同じ二項評価である。 -/
lemma gammaSmashPair_quotient_right (K L : Complex A) :
    productToSmash (gammaPointed A K) (gammaPointed A L) ≫ (gammaSmashPair A K L).right =
      gammaPair A K L :=
  congrArg Under.Hom.right (gammaSmashPair_quotient A K L)

/-- 指定 AW 単位は、smash の二項評価でも同じ右単位子を与える。 -/
lemma gammaSmashPair_right_unit (K : Complex A) :
    (gammaPointed A K ◁ gammaUnitBasedPoint A) ≫
      gammaSmashPair A K (𝟙_ (Complex A)) ≫
        (gammaPointedFunctor A).map (ρ_ K).hom = (ρ_ (gammaPointed A K)).hom := by
  let X := gammaPointed A K
  let U := gammaPointed A (𝟙_ (Complex A))
  let u := gammaUnitBasedPoint A
  have hn : (X.right ◁ u.right) ≫ productToSmash X U =
      productToSmash X (𝟙_ PointedSimplicialSet.{u}) ≫ (X ◁ u).right := by
    simpa only [Under.id_right, id_tensorHom] using
      productToSmash_naturality (𝟙 X) u
  have hu : (X.right ◁ forgetUnit) ≫
      productToSmash X (𝟙_ PointedSimplicialSet.{u}) ≫ (X ◁ u).right =
      (X.right ◁ gammaUnitPoint A) ≫ productToSmash X U := by
    rw [← hn, ← Category.assoc, ← whiskerLeft_comp]
    rw [gammaUnitBasedPoint_underlying]
  apply (cancel_epi (ρ_ X).inv).mp
  rw [Iso.inv_hom_id]
  apply Under.UnderMorphism.ext
  change (ρ_ X).inv.right ≫ (X ◁ u).right ≫
    (gammaSmashPair A K (𝟙_ (Complex A))).right ≫
      ((truncatedDoldKanFunctor A).map (ρ_ K).hom) = 𝟙 X.right
  rw [pointedSmashRightUnitor_inv]
  simp only [Category.assoc]
  slice_lhs 2 4 => exact hu
  slice_lhs 3 4 => exact gammaSmashPair_quotient_right A K (𝟙_ (Complex A))
  slice_lhs 2 4 => exact gammaPair_right_unit_point A K
  exact Iso.inv_hom_id _

end SerrePositivity.EInfinity.PowerOperation
