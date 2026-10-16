module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCoherentExtension
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeLifting

/-! # Coherent extension retaining all specified lower-dimensional chain data

Any natural system on chains below a fixed degree extends to all chains.
The actual low-degree data are retained exactly, including their faces and
degeneracies. No additional Reedy cofibrancy hypothesis on a partial
parameter inclusion is required in this degree-restricted construction.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveLowerExtension
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

abbrev LowerSystem (n : ℕ) :=
  lowerInclusion (NerveCoherentFamily.reedy D) n ⋙ NerveCoherentFamily.simplices D ⟶
    lowerInclusion (NerveCoherentFamily.reedy D) n ⋙ NerveCoherentFamily.values F

lemma square : CommSq (initial.to (NerveCoherentFamily.values F))
    (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D))
    (NerveCoherentExtension.valueProjection F) (NerveCoherentFamily.collapse (D := D)) := by
  constructor
  apply NatTrans.ext
  funext s
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

def below (n : ℕ) (a : LowerSystem F n) :
    LiftBelow (NerveCoherentFamily.reedy D) (square F) n where
  hom := a
  fac_left := by
    apply NatTrans.ext
    funext j
    exact (initialIsInitial.isInitialObj
      ((evaluation (Index D) SSet.{v}).obj j.obj) (⊥_ (Index D ⥤ SSet.{v}))).hom_ext _ _
  fac_right := by
    apply NatTrans.ext
    funext j
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

abbrev verticesApp
    (points : ∀ d : D, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d)
    (s : Lower (NerveCoherentFamily.reedy D) 1) :
    (NerveCoherentFamily.simplices D).obj s.obj ⟶ (NerveCoherentFamily.values F).obj s.obj :=
  SSet.stdSimplex.isTerminalObj₀.from _ ≫ points (endpoint s.obj)

/-- Arbitrarily prescribed objectwise points form a degree-zero natural system. -/
def vertices (points : ∀ d : D, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d) :
    LowerSystem F 1 where
  app := verticesApp F points
  naturality {s t} f := naturality_on_lower_identities (NerveCoherentFamily.reedy D) 1
    (verticesApp F points) f (RelativeLifting.degreeZero_identities
      (NerveCoherentFamily.reedy D) f.hom (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ s.property))
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ t.property)))

lemma vertices_component
    (points : ∀ d : D, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d) (d : D) :
    (vertices F points).app ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩ = points d := by
  change SSet.stdSimplex.isTerminalObj₀.from _ ≫ points d = points d
  have h : SSet.stdSimplex.isTerminalObj₀.from
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) = 𝟙 _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp]

variable [ModelCategory SSet.{v}]
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (n : ℕ) (a : LowerSystem F n)

include hp hcof in
lemma localLifting : ∀ s, HasLiftingProperty
    (relativeLatchingMap (NerveCoherentFamily.reedy D) s
      (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)))
    (relativeMatchingMap (NerveCoherentFamily.reedy D) s
      (NerveCoherentExtension.valueProjection F)) :=
  fun s => MorphismProperty.hasLiftingProperty_of_wfs _ _
    (NerveCoherentExtension.parameterCofibrant (D := D) hcof s)
    (NerveCoherentExtension.reedyRight F hp s)

/-- One global choice starting from the entire prescribed lower-degree natural system. -/
def extend : NerveCoherentFamily.System F := by
  let := localLifting F hp hcof
  exact RelativeLifting.lift (NerveCoherentFamily.reedy D) (square F) n (below F n a)

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend F hp hcof n a) = a := by
  let := localLifting F hp hcof
  exact RelativeLifting.restrict (NerveCoherentFamily.reedy D) (square F) n (below F n a)

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend F hp hcof n a).app s.obj = a.app s := congr_app (extend_restrict F hp hcof n a) s

lemma extend_chain {m : ℕ} (c : ComposableArrows D m) (hm : m < n) :
    (extend F hp hcof n a).app (ofChain c) = a.app ⟨ofChain c, hm⟩ :=
  extend_component F hp hcof n a ⟨ofChain c, hm⟩

/-- Every specified objectwise point is retained by one whole coherent system. -/
def extendVertices
    (points : ∀ d : D, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d) :
    NerveCoherentFamily.System F := extend F hp hcof 1 (vertices F points)

lemma extendVertices_point
    (points : ∀ d : D, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d) (d : D) :
    (extendVertices F hp hcof points).app (ofChain (ComposableArrows.mk₀ d)) = points d :=
  (extend_chain F hp hcof 1 (vertices F points) (ComposableArrows.mk₀ d) Nat.zero_lt_one).trans
    (vertices_component F points d)

end SerrePositivity.SimplicialModel.NerveLowerExtension
