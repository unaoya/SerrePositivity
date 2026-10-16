module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference

/-! # Labelled reference-to-row comparison on the original small raw simplex category

The row label is the actual small mixed augmentation of the raw label.
Every original degree and simplex operator is retained.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRows
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev raw : SSet.{v} :=
  OrdinaryResolutionPairs.raw.obj (OrdinaryResolutionPairs.forgetFrames.obj R)
abbrev augmentation : raw R ⟶ OrdinaryBarFirstAction.output R :=
  MixedResolutionComparison.comparison.app R

def referenceBase : (raw R).Elements ⥤ OrdinaryBarCenters.Comma R × SimplexCategoryᵒᵖ :=
  ((Functor.const _).obj (OrdinaryResolutionRows.reference R)).prod'
    (Functor.Elements.π (raw R))

def referenceLabels : (raw R).Elements ⥤
    (referenceBase R ⋙ OrdinaryBarTotalCone.values R).Elements where
  obj s := (referenceBase R ⋙ OrdinaryBarTotalCone.values R).elementsMk s s.val
  map {s t} f := Functor.Elements.homMk f (by
    change (raw R).map f.hom
      (((OrdinaryResolutionPairs.raw.map (𝟙 (OrdinaryResolutionPairs.forgetFrames.obj R))).app
        s.obj) s.val) = t.val
    rw [CategoryTheory.Functor.map_id]
    exact f.map_val)

abbrev referenceElements : (raw R).Elements ⥤ OrdinaryBarTotalCone.Total R :=
  referenceLabels R ⋙ Functor.Elements.precomp (referenceBase R) (OrdinaryBarTotalCone.values R)

abbrev rowElements : (raw R).Elements ⥤ OrdinaryBarTotalCone.Total R :=
  (augmentation R).mapElements ⋙ OrdinaryBarTotalEvaluation.rowElements R

def comparison : referenceElements R ⟶ rowElements R where
  app s := Functor.Elements.homMk
    ((OrdinaryResolutionRows.commaAugmentation R).app s.obj, 𝟙 s.obj) (by
      change ((OrdinaryResolutionPairs.raw.obj ((OrdinaryResolutionRows.rows R).obj s.obj)).map
        (𝟙 s.obj)) (((OrdinaryResolutionPairs.raw.map
          ((OrdinaryResolutionRows.augmentation R).app s.obj)).app s.obj) s.val) =
            (augmentation R).app s.obj s.val
      rw [CategoryTheory.Functor.map_id]
      rfl)
  naturality {s t} f := by
    apply Functor.Elements.hom_ext
    apply Prod.ext
    · exact (OrdinaryResolutionRows.commaAugmentation R).naturality f.hom
    · change f.hom ≫ 𝟙 t.obj = 𝟙 s.obj ≫ f.hom
      simp only [Category.comp_id, Category.id_comp]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRows
