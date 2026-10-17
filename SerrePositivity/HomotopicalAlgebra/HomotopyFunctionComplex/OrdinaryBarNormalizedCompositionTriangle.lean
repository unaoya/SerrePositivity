module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle

/-! # Native composition triangles now admit a strictly parameter-natural choice

The normalized horn operation is chosen in the original small internal
Hom, independently of T. The selected whole triangle and its comparison
edge therefore reindex strictly with all native inputs. Previous chosen
triangles are compared while fixing their two specified whole edges.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Z)

local notation "F" => nativeRestrictionComparison hcof hfib P j
  (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e
local notation "G" => compositionComparison hcof hfib P j f g c d
local notation "K" => CategoryTheory.Functor.obj (ihom (small hcof hfib X)) (small hcof hfib Z)
local notation "hK" => SimplexParameterHom.native_kan (small hcof hfib X) (small hcof hfib Z)
  (OrdinaryBarSmallReference.value_kan hcof hfib Z)

abbrev normalizedCompositionTriangle := NormalizedComparisonTriangle.build F G hK

abbrev normalizedNativeCompositionComparison :=
  KanComparisonTriangle.comparison F G (normalizedCompositionTriangle hcof hfib P j f g c d e)

variable {U : SSet.{v}} (i : U ⟶ T)

lemma normalizedCompositionTriangle_reindex :
    (normalizedCompositionTriangle hcof hfib P (UniverseLift.map i ≫ j)
      (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g)
      (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d) (UniverseLift.map i ≫ e)).triangle =
    (normalizedCompositionTriangle hcof hfib P j f g c d e).triangle ≫ (pre i).app K := by
  have hb := ComparisonTriangleTransport.hornMap_post F G
    (nativeRestrictionComparison hcof hfib P (UniverseLift.map i ≫ j)
      (lift (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g) ≫
        OrdinaryBarFixedWordResolution.composition C X Y Z) (UniverseLift.map i ≫ e))
    (compositionComparison hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
      (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d))
    ((pre i).app K) (compositeComparison_reindex hcof hfib P j f g e i)
    (inputComparison_reindex hcof hfib P j f g c d i)
  change NaturalHornFilling.fill K 2 (NormalizedTriangleHorn.section_ K 2 hK) _ = _
  rw [← hb]
  exact NaturalHornFilling.fill_reindex K 2 (NormalizedTriangleHorn.section_ K 2 hK)
    (KanComparisonTriangle.hornMap F G) i

lemma normalizedNativeCompositionComparison_reindex :
    (normalizedNativeCompositionComparison hcof hfib P (UniverseLift.map i ≫ j)
      (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g)
      (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d) (UniverseLift.map i ≫ e)).h =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
      (normalizedNativeCompositionComparison hcof hfib P j f g c d e).h := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
    (normalizedCompositionTriangle hcof hfib P (UniverseLift.map i ≫ j)
      (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g)
      (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d) (UniverseLift.map i ≫ e)).triangle) = _
  rw [normalizedCompositionTriangle_reindex, ← Category.assoc]
  exact uncurry_pre_app K
    (SSet.stdSimplex.δ (2 : Fin 3) ≫
      (normalizedCompositionTriangle hcof hfib P j f g c d e).triangle) i

def normalizeCompositionTriangleComparison : RelativeChoiceSpace.FixedBoundaryHomotopy
    (SSet.horn 2 2).ι (KanComparisonTriangle.hornMap F G)
    (compositionTriangle hcof hfib P j f g c d e).triangle
    (normalizedCompositionTriangle hcof hfib P j f g c d e).triangle :=
  NormalizedComparisonTriangle.compare F G hK (compositionTriangle hcof hfib P j f g c d e)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
