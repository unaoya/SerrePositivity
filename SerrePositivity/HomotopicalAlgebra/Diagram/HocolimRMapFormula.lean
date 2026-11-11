module

public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHocolimFrameComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.PointwiseRMapHomotopyLimit

/-! # The actual natural RMap-hocolim/holim formula

In SSet(w), with independent source object and Hom universes, the actual
bifunctors RMap(hocolim D,Y) and holim(k ↦ RMap(D(k),Y)) are joined by a
four-arrow natural weak-equivalence zigzag. The RMap at both ends uses
the same arbitrary specified source resolution and fibrant replacement.
-/

@[expose] public section
universe w v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.HocolimRMapFormula
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The actual left endpoint: the chosen small-Hom RMap at the specified hocolim. -/
abbrev source : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  (HomotopyColimit.functor K I J).op ⋙ SmallHomComparison.chosenHom cof fib

/-- The actual right endpoint: holim of the diagram of the same chosen RMap. -/
abbrev target : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  PointwiseRMapHomotopyLimit.functor K IS JS cof fib

abbrev middle₁ := SmallHocolimFrameComparison.middle K I J IS JS cof fib
abbrev bridge := SmallHocolimFrameComparison.frameHom K I J IS JS fib
abbrev middle₂ := PointwiseRMapHomotopyLimit.middle K I J IS JS cof fib

abbrev fromSource : source K I J cof fib ⟶ middle₁ K I J IS JS cof fib :=
  SmallHocolimFrameComparison.left K I J IS JS cof fib

abbrev fromBridge : bridge K I J IS JS fib ⟶ middle₁ K I J IS JS cof fib :=
  SmallHocolimFrameComparison.right K I J IS JS cof fib

abbrev bridgeToMiddle : bridge K I J IS JS fib ⟶ middle₂ K I J IS JS cof fib :=
  (SmallHocolimFrameComparison.weightedIso K I J IS JS fib).hom ≫
    HocolimWeightedComparison.toHolim K I J IS JS fib ≫
      PointwiseRMapHomotopyLimit.right K I J IS JS cof fib

abbrev fromTarget : target K IS JS cof fib ⟶ middle₂ K I J IS JS cof fib :=
  PointwiseRMapHomotopyLimit.left K I J IS JS cof fib

variable (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include hcof hfib hw in
lemma fromSource_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((fromSource K I J IS JS cof fib).app D).app Y) :=
  SmallHocolimFrameComparison.left_weakEquivalence K I J IS JS cof fib hcof hfib hw D Y

include hcof hfib in
lemma fromBridge_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((fromBridge K I J IS JS cof fib).app D).app Y) :=
  SmallHocolimFrameComparison.right_weakEquivalence K I J IS JS cof fib hcof hfib D Y

include hcof hfib in
lemma bridgeToMiddle_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((bridgeToMiddle K I J IS JS cof fib).app D).app Y) := by
  exact (weakEquivalences SSet.{w}).comp_mem _ _ ((weakEquivalences SSet.{w}).of_isIso _)
    ((weakEquivalences SSet.{w}).comp_mem _ _
      (HocolimWeightedComparison.toHolim_weakEquivalence K I J IS JS fib hcof hfib D Y)
      (PointwiseRMapHomotopyLimit.right_weakEquivalence K I J IS JS cof fib hcof hfib D Y))

include hcof hfib in
lemma fromTarget_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((fromTarget K I J IS JS cof fib).app D).app Y) :=
  PointwiseRMapHomotopyLimit.left_weakEquivalence K I J IS JS cof fib hcof hfib D Y

omit [ModelCategory C] [IsLocallyPresentable.{w} C] in
/-- Postcomposition with any ordinary localization turns a pointwise weak
natural transformation of these bifunctors into an actual isomorphism. -/
lemma isIso_localized {H : Type uH} [Category.{vH} H]
    (L : SSet.{w} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{w})]
    {F G : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w}} (a : F ⟶ G)
    (ha : ∀ D Y, weakEquivalences SSet.{w} ((a.app D).app Y)) :
    IsIso (Functor.whiskerRight a ((Functor.whiskeringRight C SSet.{w} H).obj L)) := by
  have (D : (K ⥤ C)ᵒᵖ) (Y : C) : IsIso
      (((Functor.whiskerRight a ((Functor.whiskeringRight C SSet.{w} H).obj L)).app D).app Y) :=
    Localization.inverts L (weakEquivalences SSet.{w}) _ (ha D Y)
  have (D : (K ⥤ C)ᵒᵖ) : IsIso
      ((Functor.whiskerRight a ((Functor.whiskeringRight C SSet.{w} H).obj L)).app D) :=
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

include hcof hfib hw in
/-- The final formula is natural in both variables after any ordinary
localization of SSet(w), in independent universes for its target category. -/
def localizedIso {H : Type uH} [Category.{vH} H]
    (L : SSet.{w} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{w})] :
    source K I J cof fib ⋙ (Functor.whiskeringRight C SSet.{w} H).obj L ≅
      target K IS JS cof fib ⋙ (Functor.whiskeringRight C SSet.{w} H).obj L := by
  let P := (Functor.whiskeringRight C SSet.{w} H).obj L
  have := isIso_localized K L (fromSource K I J IS JS cof fib)
    (fromSource_weakEquivalence K I J IS JS cof fib hcof hfib hw)
  have := isIso_localized K L (fromBridge K I J IS JS cof fib)
    (fromBridge_weakEquivalence K I J IS JS cof fib hcof hfib)
  have := isIso_localized K L (bridgeToMiddle K I J IS JS cof fib)
    (bridgeToMiddle_weakEquivalence K I J IS JS cof fib hcof hfib)
  have := isIso_localized K L (fromTarget K I J IS JS cof fib)
    (fromTarget_weakEquivalence K I J IS JS cof fib hcof hfib)
  exact asIso (Functor.whiskerRight (fromSource K I J IS JS cof fib) P) ≪≫
    (asIso (Functor.whiskerRight (fromBridge K I J IS JS cof fib) P)).symm ≪≫
    asIso (Functor.whiskerRight (bridgeToMiddle K I J IS JS cof fib) P) ≪≫
    (asIso (Functor.whiskerRight (fromTarget K I J IS JS cof fib) P)).symm

end SerrePositivity.DiagramModel.HocolimRMapFormula
