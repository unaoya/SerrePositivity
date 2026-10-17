module
public import SerrePositivity.DifferentialGraded.Verdier.KaroubiSquareShift

/-! # 非平坦係数変更の tria–Perf・Karoubi–Perf 正方形の shift 整合性 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Idempotents ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

instance quotientScalarTriaPerfectSquareCommShift :
    NatTrans.CommShift (quotientScalarTriaPerfectSquare φ S).hom ℤ := by
  let Q := QuotientObject D S
  let Q' := QuotientObject (DGBaseChange φ D) S
  let I := (modulePerfectOver A' Q' Set.univ).ι
  let H := triaToPerfect A Q ⋙ quotientScalarPerfectFunctor φ D S ⋙ I
  let β : (quotientScalarTriaFunctor φ S ⋙ triaToPerfect A' Q') ⋙ I ≅
      (triaToPerfect A Q ⋙ quotientScalarPerfectFunctor φ D S) ⋙ I :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ ((modulePerfectOver A' Q' Set.univ).liftCompιIso (triaInclusion A' Q') _) ≪≫
      (derivedFiniteCellOver A' Q' Set.univ).liftCompιIso H
        (quotientScalarPerfect_tria φ S) ≪≫ (Functor.associator _ _ _).symm
  have hβ : NatTrans.CommShift β.hom ℤ := by dsimp [β]; infer_instance
  have he : whiskerRight (quotientScalarTriaPerfectSquare φ S).hom I = β.hom := by
    apply NatTrans.ext
    funext X
    dsimp only [β, quotientScalarTriaPerfectSquare, whiskerRight_app, Iso.refl_hom,
      NatTrans.id_app, Iso.trans_hom, NatTrans.comp_app, associator_hom_app,
      associator_inv_app, isoWhiskerLeft_hom, whiskerLeft_app, ObjectProperty.liftCompιIso]
    rw [CategoryTheory.Functor.map_id]
    exact (show 𝟙 (H.obj X) = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ from by
      simp only [Category.id_comp])
  exact NatTrans.CommShift.of_comp_faithful (τ := (quotientScalarTriaPerfectSquare φ S).hom)
    (G := I) (h := by rw [he]; exact hβ)

instance quotientScalarKaroubiPerfectSquareCommShift :
    NatTrans.CommShift (quotientScalarKaroubiPerfectSquare φ S).hom ℤ := by
  dsimp only [quotientScalarKaroubiPerfectSquare]
  infer_instance

def quotientScalarKaroubiPerfectSquareTriangle :=
  Functor.mapTriangleIso (quotientScalarKaroubiPerfectSquare φ S)
end SerrePositivity.DifferentialGraded.DGQuotient
