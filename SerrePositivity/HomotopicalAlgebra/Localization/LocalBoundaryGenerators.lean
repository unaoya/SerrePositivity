module

public import SerrePositivity.HomotopicalAlgebra.Localization.ArrowFrameTests
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness

/-! # Small cofibration generators forcing local objects

Take the actual relative latching maps of the natural arrow frames, for
every arrow in S and every simplex degree. Right lifting at a fibrant
object forces every original locality test to be a weak equivalence.
The converse and local-equivalence of the cells are separate steps.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.LocalBoundaryGenerators
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (S : MorphismProperty C)

abbrev index := S.toSet × ℕ

abbrev arrow (i : index S) : Arrow C :=
  Arrow.mk (relativeLatchingMap simplex (SimplexCategory.mk i.2)
    ((ArrowFrames.inclusion cof).app i.1.val))

def generators : MorphismProperty C :=
  MorphismProperty.ofHoms (fun i : index S => (arrow cof S i).hom)

instance isSmall [S.IsSmall.{w}] : (generators cof S).IsSmall.{w} :=
  inferInstanceAs (MorphismProperty.ofHoms _).IsSmall

lemma generators_le_cofibrations : generators cof S ≤ cofibrations C := by
  rintro _ _ _ ⟨i⟩
  exact ArrowFrames.inclusion_reedyCofibration cof i.1.val (SimplexCategory.mk i.2)

lemma arrow_mem (i : index S) : generators cof S (arrow cof S i).hom :=
  MorphismProperty.ofHoms.mk i

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma testMap_trivialFibration_of_rlp (targetObject : C)
    (hY : (generators cof S).rlp (terminal.from targetObject)) (f : Arrow C) (hf : S f.hom) :
    trivialFibrations SSet.{v} (ArrowFrames.testMap cof f targetObject) := by
  rw [← MorphismProperty.rlp_eq_of_wfs (cofibrations SSet.{v})
    (trivialFibrations SSet.{v}), hcof, SSet.rlp_monomorphisms]
  intro A B i hi
  obtain ⟨n⟩ := hi
  have hm := arrow_mem cof S (⟨f, hf⟩, n)
  have hl := hY (arrow cof S (⟨f, hf⟩, n)).hom hm
  have : HasLiftingProperty
      (relativeLatchingMap simplex (SimplexCategory.mk n) ((ArrowFrames.inclusion cof).app f))
      (terminal.from targetObject) := hl
  exact boundary_source_lifting ((ArrowFrames.inclusion cof).app f) n

include hcof in
lemma localObjects_of_rlp
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (Y : C) [IsFibrant Y] (hY : (generators cof S).rlp (terminal.from Y)) :
    localObjects cof fib S Y := by
  apply (ArrowFrames.localObjects_iff_of_fibrant cof fib hcof S Y).mpr
  intro f hf
  exact (testMap_trivialFibration_of_rlp cof S hcof Y hY f hf).2

end SerrePositivity.Bousfield.LocalBoundaryGenerators
