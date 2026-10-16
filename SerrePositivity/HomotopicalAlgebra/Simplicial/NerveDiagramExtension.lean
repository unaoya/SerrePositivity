module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting

/-! # Relative coherent lifting for general inverse-inverting nerve value diagrams

The values can depend on both endpoints or the entire chain. Only their
inverse maps and component right lifting properties are used.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveDiagramExtension
variable {D : Type uD} [Category.{vD} D]

abbrev InvertsInverse (A : Index D ⥤ SSet.{v}) := ∀ {s t : Index D} (f : s ⟶ t),
  NerveCoherentFamily.inverse D f → IsIso (A.map f)

abbrev System (A : Index D ⥤ SSet.{v}) := NerveCoherentFamily.simplices.{vD, uD, v} D ⟶ A
abbrev LowerSystem (A : Index D ⥤ SSet.{v}) (n : ℕ) :=
  lowerInclusion (NerveCoherentFamily.reedy D) n ⋙ NerveCoherentFamily.simplices.{vD, uD, v} D ⟶
    lowerInclusion (NerveCoherentFamily.reedy D) n ⋙ A

variable (A B : Index D ⥤ SSet.{v}) (p : A ⟶ B)
  (hA : InvertsInverse A) (hB : InvertsInverse B)
  (hp : ∀ s, (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app s))

include hA hB hp in
lemma localLifting : ∀ s, HasLiftingProperty
    (relativeLatchingMap (NerveCoherentFamily.reedy D) s
      (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)))
    (relativeMatchingMap (NerveCoherentFamily.reedy D) s p) :=
  fun s => (SimplexMonomorphismLifting.reedyRight (nerve D) A B p hA hB hp s) _
    (NerveMonomorphismLifting.parameter_mono (D := D) s)

variable (target : System B) (n : ℕ) (old : LowerSystem A n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) p =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) target)

lemma square : CommSq (initial.to A)
    (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)) p target :=
  ⟨initialIsInitial.hom_ext _ _⟩

def below : LiftBelow (NerveCoherentFamily.reedy D) (square A B p target) n where
  hom := old
  fac_left := by
    apply NatTrans.ext
    funext s
    exact (initialIsInitial.isInitialObj
      ((evaluation (Index D) SSet.{v}).obj s.obj) (⊥_ (Index D ⥤ SSet.{v}))).hom_ext _ _
  fac_right := hboundary

/-- Retain the entire target system and every specified old component in a general value diagram. -/
def extend : System A := by
  let := localLifting A B p hA hB hp
  exact RelativeLifting.lift (NerveCoherentFamily.reedy D) (square A B p target) n
    (below A B p target n old hboundary)

lemma extend_boundary : extend A B p hA hB hp target n old hboundary ≫ p = target := by
  let := localLifting A B p hA hB hp
  exact RelativeLifting.fac_right (NerveCoherentFamily.reedy D) (square A B p target) n
    (below A B p target n old hboundary)

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend A B p hA hB hp target n old hboundary) = old := by
  let := localLifting A B p hA hB hp
  exact RelativeLifting.restrict (NerveCoherentFamily.reedy D) (square A B p target) n
    (below A B p target n old hboundary)

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend A B p hA hB hp target n old hboundary).app s.obj = old.app s :=
  congr_app (extend_restrict A B p hA hB hp target n old hboundary) s

end SerrePositivity.SimplicialModel.NerveDiagramExtension
