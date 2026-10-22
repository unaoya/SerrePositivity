module

public import SerrePositivity.KST.LocalizingInvariants.ProConcentratedComplexReflection
public import SerrePositivity.KST.LocalizingInvariants.ProFunctorIsoTransport
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovExtensionConeMap

/-!
概要：元の層の次数の群の pro 同型から、元の Postnikov 層複体の実 pro 逆を構成する。
方針：層ホモロジーの元の自然同型と厳密な単次数集中を使い、同じ層射へ戻す。
規約：双加群の逆はここでは主張しない。使われ方：元の平方零標的の実 pro 逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] (n : ℤ)

def postnikovLayerFunctor : NonpositiveAlgebra R ⥤ Complex R where
  obj B := postnikovLayer R B.obj n
  map f := postnikovLayerMap R f.hom n
  map_id B := postnikovLayerMap_id R n
  map_comp f g := postnikovLayerMap_comp R n f.hom g.hom

def postnikovLayerHomologyComparison :
    postnikovLayerFunctor R n ⋙ homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (-(n + 1)) ≅
      nonpositiveInclusion R ⋙ Mon.forget (Complex R) ⋙
        homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (-(n + 1)) :=
  NatIso.ofComponents (fun B => postnikovLayerHomologyIso R B.obj n)
    (fun f => postnikovLayerHomologyIso_naturality R f.hom n)

lemma postnikovLayerMap_isProIso {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1)))) :
    IsProIso (f.map (postnikovLayerFunctor R n)) := by
  have hm : IsProIso (f.map (nonpositiveInclusion R ⋙ Mon.forget (Complex R) ⋙
      homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (-(n + 1)))) :=
    TowerDiagram.proIso_of_module_groups R _ hf
  have hl := TowerDiagram.proIso_of_natIso (postnikovLayerHomologyComparison R n).symm f hm
  apply TowerDiagram.proIso_of_concentratedComplex_homology R (-(n + 1))
    (f.map (postnikovLayerFunctor R n)) (fun i => ?_) (fun i => ?_) hl
  · exact ⟨postnikovLayer_lowerBound R (A.obj i).obj n,
      postnikovLayer_upperBound R (A.obj i).obj n⟩
  · exact ⟨postnikovLayer_lowerBound R (B.obj i).obj n,
      postnikovLayer_upperBound R (B.obj i).obj n⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
