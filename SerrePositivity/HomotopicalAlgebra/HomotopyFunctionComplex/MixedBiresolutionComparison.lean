module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping

/-! # The mixed action uses the existing raw double Hom diagram

The comparison is the identity on actual arrows. The full presentation
index and all simplicial operators are retained before localization.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.MixedBiresolutionComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]

def functor : RightResolutionMapping.Index C ⥤ SSet.{v} where
  obj X := MixedDiagonalHom.obj X.1.unop.inner.resolution.obj X.2.unop.inner.resolution.obj
  map f := MixedDiagonalHom.map f.1.unop.map.diagram f.2.unop.map.diagram
  map_id X := by
    ext n h
    change 𝟙 _ ≫ h ≫ (𝟙 _).unop = h
    simp only [unop_id, Category.id_comp, Category.comp_id]
  map_comp f g := by
    ext n h
    change (g.1.unop.map.diagram.app n.unop ≫ f.1.unop.map.diagram.app n.unop) ≫ h ≫
        (g.2.unop.map.diagram.app n.unop ≫ f.2.unop.map.diagram.app n.unop).unop =
      g.1.unop.map.diagram.app n.unop ≫
        (f.1.unop.map.diagram.app n.unop ≫ h ≫ (f.2.unop.map.diagram.app n.unop).unop) ≫
          (g.2.unop.map.diagram.app n.unop).unop
    simp only [unop_comp, Category.assoc]

def component (X : RightResolutionMapping.Index C) :
    (BiresolutionRawMapping.functor (C := C)).obj X ≅ (functor (C := C)).obj X :=
  NatIso.ofComponents
    (fun n => (Equiv.refl (((BiresolutionRawMapping.functor (C := C)).obj X).obj n)).toIso) (by
    intro n m θ
    ext h
    dsimp [BiresolutionRawMapping.functor, BiresolutionRawMapping.rows,
      BiresolutionRawMapping.rawUncurried, ReplacementMapping.raw, FramedResolution.raw,
      RightResolutionMapping.presentationRows, DualResolutionTargets.framedPresentation,
      DualResolutionTargets.framedForget, DualResolutionTargets.presentations,
      DualResolutionTargets.presentation, DualResolutionTargets.diagram,
      FramedResolution.innerDiagrams, FramedResolution.forget, ResolutionObject.diagrams,
      SerrePositivity.ModelReplacement.FibrantReplacementObject.targets,
      cosimplicialHomBifunctor, cosimplicialHomMap, cosimplicialHom, functor,
      MixedDiagonalHom.obj, Equiv.toIso]
    simp only [Category.assoc]
    change X.1.unop.inner.resolution.obj.map θ.unop ≫ 𝟙 _ ≫ h ≫
        (X.2.unop.inner.resolution.obj.map θ.unop).unop =
      X.1.unop.inner.resolution.obj.map θ.unop ≫ h ≫
        (X.2.unop.inner.resolution.obj.map θ.unop).unop
    simp only [Category.id_comp])

def rawIso : BiresolutionRawMapping.functor (C := C) ≅ functor :=
  NatIso.ofComponents component (by
    intro X Y f
    ext n h
    dsimp [component, BiresolutionRawMapping.functor, BiresolutionRawMapping.rows,
      BiresolutionRawMapping.rawUncurried, ReplacementMapping.raw, FramedResolution.raw,
      RightResolutionMapping.presentationRows, DualResolutionTargets.framedPresentation,
      DualResolutionTargets.framedForget, DualResolutionTargets.presentation,
      FramedResolution.innerDiagrams, FramedResolution.forget, ResolutionObject.diagrams,
      SerrePositivity.ModelReplacement.FibrantReplacementObject.targets,
      cosimplicialHomBifunctor, cosimplicialHomMap, cosimplicialHom, functor,
      MixedDiagonalHom.map, MixedDiagonalHom.action, CosimplicialMapFamily.ofMap, Equiv.toIso]
    simp only [Category.assoc])

abbrev pair (X : ResolutionObject C) (Y : ResolutionObject Cᵒᵖ) :
    RightResolutionMapping.Index C :=
  (op (FramedResolution.ofResolution X), op (FramedResolution.ofResolution Y))

def action (X X' : ResolutionObject C) (f : X.base ⟶ X'.base)
    (Y Y' : ResolutionObject Cᵒᵖ) (g : Y.base ⟶ Y'.base) {T : SSet.{v}}
    (s : T ⟶ ResolutionLiftSpace.obj X X' f) (r : T ⟶ ResolutionLiftSpace.obj Y Y' g)
    (t : T ⟶ (BiresolutionRawMapping.functor.obj (pair X' Y'))) :
    T ⟶ MixedResolutionLiftAction.output X Y :=
  MixedResolutionLiftAction.action X X' f Y Y' g s r (t ≫ rawIso.hom.app (pair X' Y'))

end SerrePositivity.HomotopyFunctionComplex.MixedBiresolutionComparison
