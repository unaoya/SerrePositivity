module

public import SerrePositivity.KST.Spectra.WeightCylinderBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting

/-!
概要：相対 matching が全ての単射への RLP を持つ射の下で図式ホモトピーを構成する。
方針：Reedy cofibrant な源の境界 cylinder に対して Reedy の逐次持ち上げを行う。
規約：filler は図式の自然変換全体として構成し、両端と下の射を厳密に保つ。
使われ方：Goerss–Jardine VII §4。二射影の切断を図式ホモトピー逆へ送る。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.Reedy SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.WeightCylinderLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- tensor した境界包含の後でパラメーターを忘れると元の境界の射影になる。 -/
lemma map_projection (F : CosimplicialObject SSet.{u}) {A B : SSet.{u}} (i : A ⟶ B) :
    WeightTensorLatching.map F i ≫ WeightCylinderBoundary.projection F B =
      WeightCylinderBoundary.projection F A := by
  apply NatTrans.ext
  funext j
  exact whiskerLeft_fst (F.obj j) i

/-- 同じ下の射を持つ二つの図式の射を、下で固定された cylinder で結ぶ。 -/
lemma exists_vertical_homotopy {F X Y : CosimplicialObject SSet.{u}}
    (hF : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (initial.to F))
    (p : X ⟶ Y)
    (hp : reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp p)
    (f g : F ⟶ X) (h : f ≫ p = g ≫ p) :
    ∃ H : WeightTensorLatching.diagram F (Δ[1] : SSet.{u}) ⟶ X,
      (∀ j, SSet.ι₀ ≫ H.app j = f.app j) ∧
      (∀ j, SSet.ι₁ ≫ H.app j = g.app j) ∧
      H ≫ p = WeightCylinderBoundary.projection F (Δ[1] : SSet.{u}) ≫ f ≫ p := by
  let i := WeightTensorLatching.map F (boundary 1).ι
  have hi := WeightTensorLatching.map_reedy_mono F hF (boundary 1).ι
  let : ∀ j, HasLiftingProperty (relativeLatchingMap simplex j i)
      (relativeMatchingMap simplex j p) := fun j ↦ hp j _ (hi j)
  let : HasLiftingProperty i p := Lifting.hasLiftingProperty simplex
  let b := WeightCylinderBoundary.projection F (Δ[1] : SSet.{u}) ≫ f ≫ p
  let sq : CommSq (WeightCylinderBoundary.family f g) i p b := ⟨by
    rw [WeightCylinderBoundary.family_projection f g p h]
    dsimp only [b, i]
    rw [← Category.assoc, ← Category.assoc, map_projection, Category.assoc]⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · intro j
    have hj := NatTrans.congr_app sq.fac_left j
    change (F.obj j ◁ (boundary 1).ι) ≫ sq.lift.app j = boundaryMap (f.app j) (g.app j) at hj
    rw [← section_zero (F.obj j), Category.assoc, ← boundary.ι_ι (1 : Fin 2),
      whiskerLeft_comp, Category.assoc, hj, boundaryMap_zero]
    rfl
  · intro j
    have hj := NatTrans.congr_app sq.fac_left j
    change (F.obj j ◁ (boundary 1).ι) ≫ sq.lift.app j = boundaryMap (f.app j) (g.app j) at hj
    rw [← section_one (F.obj j), Category.assoc, ← boundary.ι_ι (0 : Fin 2),
      whiskerLeft_comp, Category.assoc, hj, boundaryMap_one]
    rfl

end
end SerrePositivity.KST.Spectra.WeightCylinderLifting
