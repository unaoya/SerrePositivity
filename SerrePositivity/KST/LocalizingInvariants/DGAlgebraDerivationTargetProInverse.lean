module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerProInverse
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassCospanFunctor
public import SerrePositivity.KST.LocalizingInvariants.ProFunctorProduct
public import SerrePositivity.KST.LocalizingInvariants.ProMonoidReflection

/-!
概要：元の底と層の実 pro 逆から、元の Postnikov 平方零標的の実代数 pro 逆を構成。
方針：直和の二座標を元の射と自然同型で比較し、単位・積を回収する。
規約：双加群の逆を入力しない。使われ方：元の class 図式の中心の実 pro 逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
open ProExcision
variable (R : Type u) [CommRing R]

def cochainBiproductFunctor : (Complex R × Complex R) ⥤ Complex R where
  obj X := X.1 ⊞ X.2
  map f := biprod.map f.1 f.2
  map_id X := cochainBiprodMap_id
  map_comp f g := (cochainBiprodMap_comp _ _ _ _).symm

namespace DGAlgebra
variable (n : ℤ) (hn : 0 ≤ n)

def postnikovDerivationTargetFunctor : NonpositiveAlgebra R ⥤ Mon (Complex R) :=
  postnikovClassCospanFunctor R n hn ⋙ (CategoryTheory.evaluation _ _).obj WalkingCospan.one

def postnikovDerivationTargetComplexIso :
    (((postnikovFunctor R n ⋙ Mon.forget (Complex R)).prod'
      (postnikovLayerFunctor R n ⋙ CategoryTheory.shiftFunctor (Complex R) (1 : ℤ))) ⋙
        cochainBiproductFunctor R) ≅
      postnikovDerivationTargetFunctor R n hn ⋙ Mon.forget (Complex R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change biprod.map (postnikovMap R f.hom n).hom ((postnikovLayerMap R f.hom n)⟦(1 : ℤ)⟧') ≫
      𝟙 _ = 𝟙 _ ≫ (postnikovDerivationTargetMap R f.hom n hn).hom
    rw [Category.comp_id, Category.id_comp]
    exact (postnikovDerivationTargetMap_hom R f.hom n hn).symm)

lemma postnikovDerivationTargetMap_isProIso {A B : Tower (NonpositiveAlgebra R)}
    (f : LevelHom A B) (hB : IsProIso (f.map (postnikovFunctor R n)))
    (hM : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1)))) :
    IsProIso (f.map (postnikovDerivationTargetFunctor R n hn)) := by
  have hl := (postnikovLayerMap_isProIso R n f hM).map
    (CategoryTheory.shiftFunctor (Complex R) (1 : ℤ))
  have hp := (TowerDiagram.proIso_prod'
    (F := postnikovFunctor R n ⋙ Mon.forget (Complex R))
    (G := postnikovLayerFunctor R n ⋙ CategoryTheory.shiftFunctor (Complex R) (1 : ℤ))
    f (hB.map (Mon.forget (Complex R))) hl).map (cochainBiproductFunctor R)
  have hc := TowerDiagram.proIso_of_natIso (postnikovDerivationTargetComplexIso R n hn) f hp
  exact TowerDiagram.proIso_of_monoid_forget _ hc

end DGAlgebra
end SerrePositivity.KST.LocalizingInvariants
