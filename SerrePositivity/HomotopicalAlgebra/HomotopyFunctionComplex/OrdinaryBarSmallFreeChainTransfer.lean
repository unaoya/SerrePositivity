module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer

/-! # Native small parameter families for arbitrary actual free-resolution chains

Pulling the entire simplex parameter back to a lifted small parameter and
lowering the resulting tensor family preserves every face and degeneracy,
and both zero/one composition laws with arbitrary prefixes and suffixes.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) {T U : SSet.{v}}
  (j : UniverseLift.obj.{max u v} T ⟶ parameters P n)

def family {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    small hcof hfib X ⊗ T ⟶ small hcof hfib Y :=
  UniverseLift.lowerTensor (OrdinaryBarFreeChainTransfer.family hcof hfib P n j q t)

lemma family_substitute (k : U ⟶ T) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    family hcof hfib P n (UniverseLift.map k ≫ j) q (fun r => UniverseLift.map k ≫ t r) =
      ParameterComposition.substitute k (family hcof hfib P n j q t) := by
  rw [family, OrdinaryBarFreeChainTransfer.family_substitute]
  ext m x
  rfl

lemma family_nil (X : degree (D C) (n + 1))
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    family hcof hfib P n j (Quiver.Path.nil : Quiver.Path X X) t = fst (small hcof hfib X) T := by
  rw [family, OrdinaryBarFreeChainTransfer.family_nil]
  ext m x
  rfl

lemma family_face (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    family hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
      family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q t :=
  congrArg UniverseLift.lowerTensor (OrdinaryBarFreeChainTransfer.family_face hcof hfib P n j i q t)

lemma family_degeneracy (i : Fin (n + 1))
    (k : UniverseLift.obj.{max u v} T ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    family hcof hfib P (n + 1) k ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q) t =
      family hcof hfib P n (k ≫ P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i) q t :=
  congrArg UniverseLift.lowerTensor
    (OrdinaryBarFreeChainTransfer.family_degeneracy hcof hfib P n i k q t)

lemma zero_face {a d : D C} {X Y Z : degree (D C) (n + 1)}
    (q : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) a X)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)
    (r : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) Z d) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
      ((OrdinaryBarFreeChainTransfer.snoc hcof hfib P n j
        (OrdinaryBarFreeChainTransfer.snoc hcof hfib P n j q f
          (RetractChainFamily.zero _)) g t).append r) =
    OrdinaryBarChainFamily.smallFamily hcof hfib
      ((OrdinaryBarFreeChainTransfer.snoc hcof hfib P n j q (f ≫ g) t).append r) :=
  congrArg UniverseLift.lowerTensor
    (OrdinaryBarFreeChainTransfer.zero_face hcof hfib P n j q f g t r)

lemma one_face {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) a X) (f : X ⟶ Y)
    (r : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) Y d) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
      ((OrdinaryBarFreeChainTransfer.snoc hcof hfib P n j q f
        (RetractChainFamily.one _)).append r) =
    ParameterComposition.comp
      (OrdinaryBarChainFamily.smallFamily hcof hfib
        (OrdinaryBarFreeChainTransfer.snoc hcof hfib P n j q f (RetractChainFamily.zero _)))
      (OrdinaryBarChainFamily.smallFamily hcof hfib r) := by
  rw [OrdinaryBarChainFamily.smallFamily, OrdinaryBarFreeChainTransfer.one_face]
  ext m x
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer
