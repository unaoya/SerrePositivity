module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom

/-! # The actual universe comparison commutes with currying whole small families -/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.UniverseLiftClosedCurry

lemma nativeEquiv_symm_curry {K P T : SSet.{v}} (f : K ⊗ T ⟶ P)
    (n : SimplexCategory) (t : T.obj (Opposite.op n)) :
    (SimplexParameterHom.nativeEquiv K P n).symm ((curry f).app (Opposite.op n) t) =
      K ◁ SSet.yonedaEquiv.symm t ≫ f := by
  apply (SimplexParameterHom.nativeEquiv K P n).injective
  rw [Equiv.apply_symm_apply]
  change (curry f).app (Opposite.op n) t =
    SSet.yonedaEquiv (curry (K ◁ SSet.yonedaEquiv.symm t ≫ f))
  rw [curry_natural_left]
  rw [SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]

lemma curry_tensorMap {K P T : SSet.{v}} (f : K ⊗ T ⟶ P) :
    UniverseLift.map.{w} (curry f) ≫ (UniverseLiftParameterHom.closedIso K P).hom =
      curry (UniverseLift.tensorMap.{w} f) := by
  ext n x
  change SimplexParameterHom.nativeEquiv (UniverseLift.obj.{w} K) (UniverseLift.obj.{w} P) n.unop
    (UniverseLift.simplexTensorMap ((SimplexParameterHom.nativeEquiv K P n.unop).symm
      ((curry f).app n x.down))) = (curry (UniverseLift.tensorMap.{w} f)).app n x
  rw [nativeEquiv_symm_curry]
  apply (SimplexParameterHom.nativeEquiv (UniverseLift.obj.{w} K)
    (UniverseLift.obj.{w} P) n.unop).symm.injective
  rw [Equiv.symm_apply_apply, nativeEquiv_symm_curry]
  ext m y
  rfl

lemma curry_lowerTensor {K P T : SSet.{v}}
    (f : UniverseLift.obj.{w} K ⊗ UniverseLift.obj.{w} T ⟶ UniverseLift.obj.{w} P) :
    UniverseLift.map.{w} (curry (UniverseLift.lowerTensor f)) ≫
        (UniverseLiftParameterHom.closedIso K P).hom = curry f := by
  rw [curry_tensorMap, UniverseLift.tensorMap_lowerTensor]

lemma evaluation (K P : SSet.{v}) :
    UniverseLift.obj.{w} K ◁ (UniverseLiftParameterHom.closedIso K P).hom ≫
      (ihom.ev (UniverseLift.obj K)).app (UniverseLift.obj P) =
        UniverseLift.tensorMap.{w} ((ihom.ev K).app P) := by
  have h := curry_tensorMap.{w} ((ihom.ev K).app P)
  rw [← uncurry_id_eq_ev, curry_uncurry] at h
  have hi : UniverseLift.map.{w} (𝟙 ((ihom K).obj P)) =
      𝟙 (UniverseLift.obj.{w} ((ihom K).obj P)) := rfl
  rw [hi, Category.id_comp] at h
  have hh := congrArg uncurry h
  rw [uncurry_curry, uncurry_eq] at hh
  exact hh

end SerrePositivity.SimplicialModel.UniverseLiftClosedCurry
