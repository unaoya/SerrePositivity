module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerAlgebra
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraDerivationTargetProInverse

/-!
概要：零切断と未 shift 層の平方零代数を、元の代数の厳密な関手にする。
方針：元の二成分の恒等合成則を underlying 直和で回収する。
規約：対象ごとの同型で自然性を代用しない。使われ方：π₀・高次群から実代数 pro 逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (n : ℤ)

def postnikovZeroLayerAlgebraFunctor : NonpositiveAlgebra R ⥤ Mon (Complex R) where
  obj B := postnikovZeroLayerAlgebra R B.obj n
  map f := postnikovZeroLayerAlgebraMap R n f.hom
  map_id B := by
    apply Mon.Hom.ext
    change biprod.map (postnikovMap R (𝟙 B.obj) 0).hom
      (postnikovLayerMap R (𝟙 B.obj) n) = 𝟙 ((postnikov R B.obj 0).X ⊞ postnikovLayer R B.obj n)
    rw [postnikovMap_identity, postnikovLayerMap_id]
    exact cochainBiprodMap_id
  map_comp f g := by
    apply Mon.Hom.ext
    change (postnikovZeroLayerAlgebraMap R n (f.hom ≫ g.hom)).hom =
      (postnikovZeroLayerAlgebraMap R n f.hom).hom ≫
        (postnikovZeroLayerAlgebraMap R n g.hom).hom
    rw [postnikovZeroLayerAlgebraMap_hom, postnikovZeroLayerAlgebraMap_hom,
      postnikovZeroLayerAlgebraMap_hom, postnikovLayerMap_comp]
    have h := congrArg Mon.Hom.hom (postnikovMap_composition R 0 f.hom g.hom)
    rw [h]
    exact (cochainBiprodMap_comp _ _ _ _).symm

def postnikovZeroLayerAlgebraComplexIso :
    (((postnikovFunctor R 0 ⋙ Mon.forget (Complex R)).prod' (postnikovLayerFunctor R n)) ⋙
      cochainBiproductFunctor R) ≅ postnikovZeroLayerAlgebraFunctor R n ⋙ Mon.forget (Complex R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change biprod.map (postnikovMap R f.hom 0).hom (postnikovLayerMap R f.hom n) ≫ 𝟙 _ =
      𝟙 _ ≫ (postnikovZeroLayerAlgebraMap R n f.hom).hom
    rw [Category.comp_id, Category.id_comp]
    exact (postnikovZeroLayerAlgebraMap_hom R n f.hom).symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
