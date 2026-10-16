module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameter
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveDiagramExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveLargeParameter

/-! # Whole coherent families for parameters moving with the center

A chain uses its first parameter space and last small value. No model
structure in the larger auxiliary mapping-space universe is needed.
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveMovingParameter
variable {D : Type uD} [Category.{vD} D]
  (K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v})
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d))

abbrev lifted := NerveLargeParameter.lifted.{w} F
abbrev values := NerveBiparameter.values K (lifted F)
abbrev System := NerveBiparameter.System K (lifted F)
abbrev LowerSystem (n : ℕ) := NerveDiagramExtension.LowerSystem (values K F) n
abbrev point : Index D ⥤ SSet.{w} := (Functor.const (Index D)).obj
  (SSet.stdSimplex.obj (SimplexCategory.mk 0))

def projection : values K F ⟶ point.{max w v} (D := D) where
  app _ := SSet.stdSimplex.isTerminalObj₀.from _
  naturality {_ _} _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

include hp in
lemma rightLifting : ∀ s, (MorphismProperty.monomorphisms SSet.{max w v}).rlp
    ((projection K F).app s) := fun s =>
  BoundaryFillerLifting.terminal_rightLifting
    (LargeParameterMapping.fillers (hp (endpoint s)) (K.obj (NerveSimplexStart.start s)))

lemma values_inverts : NerveDiagramExtension.InvertsInverse (values K F) :=
  NerveBiparameter.values_map_isIso K (lifted F)

lemma point_inverts : NerveDiagramExtension.InvertsInverse (point.{w} (D := D)) := by
  intro s t f _hf
  change IsIso (𝟙 _)
  infer_instance

lemma boundary (n : ℕ) (old : LowerSystem K F n) : old ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) (projection K F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (NerveCoherentFamily.collapse (D := D)) := by
  apply NatTrans.ext
  funext s
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Extend an entire lower system in the changing-parameter/endpoint diagram. -/
def extend (n : ℕ) (old : LowerSystem K F n) : System K F :=
  NerveDiagramExtension.extend (values K F) (point.{max w v} (D := D)) (projection K F)
    (values_inverts K F) (point_inverts.{max w v}) (rightLifting K F hp)
    (NerveCoherentFamily.collapse (D := D)) n old (boundary K F n old)

lemma extend_restrict (n : ℕ) (old : LowerSystem K F n) :
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (extend K F hp n old) = old := NerveDiagramExtension.extend_restrict _ _ _ _ _ _ _ _ _ _

lemma extend_component (n : ℕ) (old : LowerSystem K F n)
    (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend K F hp n old).app s.obj = old.app s := congr_app (extend_restrict K F hp n old) s

lemma start_eq_endpoint_zero (s : Index D) (h : dimension s = 0) :
    NerveSimplexStart.start s = endpoint s := by
  apply congrArg (chain s).obj
  apply Fin.ext
  exact h.symm

variable (families : ∀ d, K.obj d ⟶ UniverseLift.obj.{w} (F.obj d))

abbrev vertexPoint (s : Lower (NerveCoherentFamily.reedy D) 1) :
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 0) ⟶ (values K F).obj s.obj :=
  RelativeChoiceSpace.name (families (NerveSimplexStart.start s.obj) ≫
    eqToHom (congrArg (lifted F).obj (start_eq_endpoint_zero s.obj
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ s.property)))))

abbrev verticesApp (s : Lower (NerveCoherentFamily.reedy D) 1) :=
  SSet.stdSimplex.isTerminalObj₀.from ((NerveCoherentFamily.simplices D).obj s.obj) ≫
    vertexPoint K F families s

/-- Independent whole moving families form one natural degree-zero system. -/
def vertices : LowerSystem K F 1 where
  app := verticesApp K F families
  naturality {s t} f := naturality_on_lower_identities (NerveCoherentFamily.reedy D) 1
    (verticesApp K F families) f (RelativeLifting.degreeZero_identities
      (NerveCoherentFamily.reedy D) f.hom (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ s.property))
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ t.property)))

lemma vertices_at_object (d : D) :
    (vertices K F families).app ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩ =
      RelativeChoiceSpace.name (families d) := by
  change SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name (families d ≫ 𝟙 _) = _
  rw [Category.comp_id]
  have h : SSet.stdSimplex.isTerminalObj₀.from
      (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 0)) = 𝟙 _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact (congrArg (fun k => k ≫ RelativeChoiceSpace.name (families d)) h).trans
    (Category.id_comp _)

def extendFamilies : System K F := extend K F hp 1 (vertices K F families)

abbrev evaluate (a : System K F) (d : D) : K.obj d ⟶ UniverseLift.obj.{w} (F.obj d) :=
  uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫ a.app (ofChain (ComposableArrows.mk₀ d)))

lemma extendFamilies_evaluate (d : D) : evaluate K F (extendFamilies K F hp families) d =
    families d := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (extendFamilies K F hp families).app (ofChain (ComposableArrows.mk₀ d))) = families d
  rw [show (extendFamilies K F hp families).app (ofChain (ComposableArrows.mk₀ d)) =
      RelativeChoiceSpace.name (families d) from
    (extend_component K F hp 1 (vertices K F families)
      ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩).trans
        (vertices_at_object K F families d)]
  simp only [RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

end SerrePositivity.SimplicialModel.NerveMovingParameter
