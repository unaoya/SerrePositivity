module

public import SerrePositivity.KST.Spectra.PointedUncurryActionTensor
public import SerrePositivity.KST.Spectra.InternalHomTensorCotensor
public import SerrePositivity.KST.Spectra.PointedParametricPostExchange

/-!
概要：全パラメータを保った元の uncurry 座標写像と、その標準族作用との厳密整合性。
方針：通常円とパラメータを交換し、同じテンソル curry の逆射を作用させる。
規約：区間を再選択しない。使われ方：実際の全 Hom 自然性正方形と四三角形の同時移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 通常円と全パラメータを交換して、元の同じ uncurry 作用を施す座標射。 -/
def parametricUncurryAction (A P W : PointedSimplicialSet.{u}) :
    PointedObject.basedHom A (PointedObject.basedHom P (loopSpace W)) ⟶
      PointedObject.basedHom (suspension A) (PointedObject.basedHom P W) :=
  PointedObject.basedHomMap A (InternalHomExchange.iso PointedSimplicialSet.circle.{u} P W).inv ≫
    uncurryAction A (PointedObject.basedHom P W)

/-- 同じ座標射は、元の uncurry のパラメータ内部 Hom 像を二つの交換で挟んだ射。 -/
lemma parametricUncurryAction_exchange (A P W : PointedSimplicialSet.{u}) :
    parametricUncurryAction A P W =
      (InternalHomExchange.iso A P (loopSpace W)).hom ≫
        PointedObject.basedHomMap P (uncurryAction A W) ≫
          (InternalHomExchange.iso (suspension A) P W).inv := by
  let C : PointedSimplicialSet.{u} := PointedSimplicialSet.circle.{u}
  dsimp only [parametricUncurryAction]
  rw [uncurryAction_eq_tensor_inv, uncurryAction_eq_tensor_inv]
  change (ihom A).map (InternalHomExchange.iso C P W).inv ≫
      (InternalHomTensor.iso C A ((ihom P).obj W)).inv =
    (InternalHomExchange.iso A P ((ihom C).obj W)).hom ≫
      (ihom P).map (InternalHomTensor.iso C A W).inv ≫
        (InternalHomExchange.iso (C ⊗ A) P W).inv
  have h := InternalHomExchange.tensor_curry C A P W
  apply (cancel_epi ((InternalHomTensor.iso C A ((ihom P).obj W)).hom ≫
    (ihom A).map (InternalHomExchange.iso C P W).hom)).mp
  have hx := ((InternalHomTensor.iso C A ((ihom P).obj W)) ≪≫
    (ihom A).mapIso (InternalHomExchange.iso C P W)).hom_inv_id
  have hy := ((InternalHomExchange.iso (C ⊗ A) P W) ≪≫
    (ihom P).mapIso (InternalHomTensor.iso C A W)).hom_inv_id
  have hz : ((InternalHomTensor.iso C A ((ihom P).obj W)).hom ≫
      (ihom A).map (InternalHomExchange.iso C P W).hom) ≫
        (InternalHomExchange.iso A P ((ihom C).obj W)).hom =
      (InternalHomExchange.iso (C ⊗ A) P W).hom ≫
        (ihom P).map (InternalHomTensor.iso C A W).hom := by
    simpa only [Category.assoc] using h.symm
  calc
    _ = 𝟙 _ := hx
    _ = (((InternalHomTensor.iso C A ((ihom P).obj W)).hom ≫
          (ihom A).map (InternalHomExchange.iso C P W).hom) ≫
            (InternalHomExchange.iso A P ((ihom C).obj W)).hom) ≫
        ((ihom P).map (InternalHomTensor.iso C A W).inv ≫
          (InternalHomExchange.iso (C ⊗ A) P W).inv) := by
      rw [hz]
      exact hy.symm
    _ = _ := Category.assoc _ _ _


/-- 標準全族作用後の同じ uncurry は、転置した族への元の uncurry の後合成。 -/
lemma parametricUncurryAction_post (A : PointedSimplicialSet.{u})
    {P V W : PointedSimplicialSet.{u}} (v : P ⟶ PointedObject.basedHom V W) :
    PointedObject.basedHomMap A (parametricPost PointedSimplicialSet.circle.{u} v) ≫
        parametricUncurryAction A P W =
      uncurryAction A V ≫ PointedObject.basedHomMap (suspension A) (transpose v) := by
  have he : PointedObject.basedHomMap A
        (parametricPost PointedSimplicialSet.circle.{u} v) ≫
      PointedObject.basedHomMap A
        (InternalHomExchange.iso PointedSimplicialSet.circle.{u} P W).inv =
    PointedObject.basedHomMap A
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (transpose v)) := by
    change (ihom A).map (parametricPost PointedSimplicialSet.circle.{u} v) ≫
        (ihom A).map (InternalHomExchange.iso PointedSimplicialSet.circle.{u} P W).inv = _
    rw [← CategoryTheory.Functor.map_comp, parametricPost_exchange, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    rfl
  dsimp only [parametricUncurryAction]
  rw [← Category.assoc, he]
  exact uncurryAction_post A (transpose v)

end SerrePositivity.KST.Spectra.PointedMapping
