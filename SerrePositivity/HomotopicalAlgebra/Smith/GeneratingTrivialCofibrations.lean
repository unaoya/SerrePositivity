module

public import SerrePositivity.HomotopicalAlgebra.Smith.SolutionSet
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness
public import SerrePositivity.HomotopicalAlgebra.Generated.Basic

/-! # The small generating trivial cofibration class in Smith recognition

A solution square is refined using a pushout and the I-factorization. This
puts its middle arrow in `I.rlp.llp ⊓ W` without losing square factorization.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C] (I W : MorphismProperty C)

/-- A square factored through an acyclic generated cofibration. -/
structure RefinedSquare (i f : Arrow C) (sq : i ⟶ f) where
  arrow : Arrow C
  cof : I.rlp.llp arrow.hom
  weak : W arrow.hom
  toMiddle : i ⟶ arrow
  fromMiddle : arrow ⟶ f
  fac : toMiddle ≫ fromMiddle = sq

variable [HasPushouts C] [I.HasSmallObjectArgument.{w}]
  [W.HasTwoOutOfThreeProperty]

/-- The pushout ensures the refined map, rather than just the factor map, is a cofibration. -/
def refineSquare (hIW : I.rlp ≤ W) (i f : Arrow C) (hi : I i.hom)
    (hf : W f.hom) (sq : i ⟶ f) : RefinedSquare I W i f sq := by
  let d := pushout.desc sq.right f.hom sq.w.symm
  let fac := MorphismProperty.factorizationData I.rlp.llp I.rlp d
  let j := pushout.inr i.hom sq.left ≫ fac.i
  have hj : I.rlp.llp j := (I.rlp.llp).comp_mem _ _
    ((I.rlp.llp).pushout_inr _ _ (I.le_llp_rlp _ hi)) fac.hi
  have hjp : j ≫ fac.p = f.hom := by simp [j, Category.assoc, d]
  refine { arrow := Arrow.mk j
           cof := hj
           weak := W.of_postcomp j fac.p (hIW _ fac.hp) (hjp ▸ hf)
           toMiddle := Arrow.homMk sq.left (pushout.inl i.hom sq.left ≫ fac.i) ?_
           fromMiddle := Arrow.homMk (𝟙 _) fac.p (by simpa using hjp.symm)
           fac := ?_ }
  · dsimp [j]
    rw [← Category.assoc, ← pushout.condition, Category.assoc]
  · ext
    · simp
    · simp [Category.assoc, d]

variable [IsAccessibleCategory.{w} (Arrow C)]
  [IsAccessibleCategory.{w} (arrowProperty W).FullSubcategory]
  [(arrowInclusion W).IsAccessible.{w}]

/-- The index is the small union of R0 solution families over I. -/
abbrev generatingTrivialIndex := Σ i : I.toSet, solutionIndex W i.val

def generatingTrivialSquare (hIW : I.rlp ≤ W) (x : generatingTrivialIndex I W) :=
  refineSquare I W hIW x.1.val (solutionArrow W x.1.val x.2).obj x.1.property
    (solutionArrow W x.1.val x.2).property (solutionSquare W x.1.val x.2)

/-- J is constructed, rather than supplied as an input. -/
def generatingTrivialCofibrations (hIW : I.rlp ≤ W) : MorphismProperty C :=
  MorphismProperty.ofHoms (fun x : generatingTrivialIndex I W ↦
    (generatingTrivialSquare I W hIW x).arrow.hom)

instance generatingTrivialCofibrations_isSmall [I.IsSmall.{w}] (hIW : I.rlp ≤ W) :
    (generatingTrivialCofibrations I W hIW).IsSmall.{w} := inferInstanceAs
      (MorphismProperty.ofHoms _).IsSmall

lemma generatingTrivialCofibrations_le (hIW : I.rlp ≤ W) :
    generatingTrivialCofibrations I W hIW ≤ I.rlp.llp ⊓ W := by
  rintro _ _ _ ⟨x⟩
  exact ⟨(generatingTrivialSquare I W hIW x).cof,
    (generatingTrivialSquare I W hIW x).weak⟩

lemma generatingTrivialCofibrations_factor (hIW : I.rlp ≤ W)
    (i f : Arrow C) (hi : I i.hom) (hf : W f.hom) (sq : i ⟶ f) :
    ∃ g : Arrow C, generatingTrivialCofibrations I W hIW g.hom ∧
      ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq := by
  obtain ⟨j, q, hq⟩ := solutionSquare_factor W i f hf sq
  let x : generatingTrivialIndex I W := ⟨⟨i, hi⟩, j⟩
  let r := generatingTrivialSquare I W hIW x
  refine ⟨r.arrow, ?_, r.toMiddle, r.fromMiddle ≫ q, ?_⟩
  · exact MorphismProperty.ofHoms.mk
      (f := fun x : generatingTrivialIndex I W ↦
        (generatingTrivialSquare I W hIW x).arrow.hom) x
  · rw [← Category.assoc, r.fac]
    exact hq

end SerrePositivity.Smith
