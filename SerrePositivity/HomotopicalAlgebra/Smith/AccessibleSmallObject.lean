module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleCellAttachment
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleIteration
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness

/-! # Accessibility of Mathlib's actual small-object factorization

The construction ordinal and the accessibility cardinal are independent.
Accessibility of the successor is derived from the generators, then propagated
through the actual transfinite iteration and its endpoint projection.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.AccessibleSmallObject
variable {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (I : MorphismProperty C) (μ : Cardinal.{w}) [Fact μ.IsRegular]
  [OrderBot μ.ord.ToType] [I.IsCardinalForSmallObjectArgument μ]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [∀ i : I.toSet, IsCardinalPresentable i.val.left κ]
  [∀ i : I.toSet, IsCardinalPresentable i.val.right κ]

lemma iteration_isCardinalAccessible :
    (SmallObject.iteration I μ).IsCardinalAccessible κ := by
  have := SmallObject.isSmall I μ
  let a : I.toSet → Arrow C := fun i ↦ i.val
  have : ∀ {X Y : C} (f : X ⟶ Y),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex I.homFamily f)) C :=
    fun f ↦ SmallObject.hasColimitsOfShape_discrete I μ _ _ f
  have : (SmallObject.functor I.homFamily).IsCardinalAccessible κ :=
    AccessibleCellAttachment.step_isCardinalAccessible a κ
  exact AccessibleIteration.iteration_isCardinalAccessible
    (SmallObject.functor I.homFamily) (SmallObject.ε I.homFamily) κ

lemma factorization_isCardinalAccessible :
    (SmallObject.functorialFactorizationData I μ).Z.IsCardinalAccessible κ := by
  have := iteration_isCardinalAccessible I μ κ
  have := AccessibleFactorization.arrow_left_isCardinalAccessible (C := C) κ
  exact inferInstanceAs
    ((SmallObject.iteration I μ ⋙ Arrow.leftFunc).IsCardinalAccessible κ)

lemma leftFactor_isCardinalAccessible :
    (AccessibleFactorization.leftFactor
      (SmallObject.functorialFactorizationData I μ)).IsCardinalAccessible κ := by
  have := factorization_isCardinalAccessible I μ κ
  exact AccessibleFactorization.leftFactor_isCardinalAccessible _ κ

lemma rightFactor_isCardinalAccessible :
    (AccessibleFactorization.rightFactor
      (SmallObject.functorialFactorizationData I μ)).IsCardinalAccessible κ := by
  have := factorization_isCardinalAccessible I μ κ
  exact AccessibleFactorization.rightFactor_isCardinalAccessible _ κ

/-- A specified accessibility cardinal for the generators suffices; the SOA
construction may use an independent ordinal. -/
lemma exists_factorization_at (I : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i : I.toSet, IsCardinalPresentable i.val.left κ]
    [∀ i : I.toSet, IsCardinalPresentable i.val.right κ] :
    ∃ d : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp,
      d.Z.IsCardinalAccessible κ ∧
      (AccessibleFactorization.leftFactor d).IsCardinalAccessible κ ∧
      (AccessibleFactorization.rightFactor d).IsCardinalAccessible κ := by
  obtain ⟨μ, hμ, hbot, hI⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := I)
  exact ⟨SmallObject.functorialFactorizationData I μ,
    factorization_isCardinalAccessible I μ κ,
    leftFactor_isCardinalAccessible I μ κ, rightFactor_isCardinalAccessible I μ κ⟩

/-- Local presentability and a small generator class supply both the SOA and
one common regular accessibility cardinal for all three factorization functors. -/
lemma exists_accessible_factorization [IsLocallyPresentable.{w} C]
    (I : MorphismProperty C) [I.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp,
        d.Z.IsCardinalAccessible κ ∧
        (AccessibleFactorization.leftFactor d).IsCardinalAccessible κ ∧
        (AccessibleFactorization.rightFactor d).IsCardinalAccessible κ := by
  have := hasSmallObjectArgument I
  obtain ⟨κ, hκ, ha⟩ := exists_common_arrow_presentability (fun i : I.toSet ↦ i.val)
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.left κ := fun i ↦ (ha i).1
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.right κ := fun i ↦ (ha i).2
  exact ⟨κ, hκ, exists_factorization_at I κ⟩

end SerrePositivity.Smith.AccessibleSmallObject

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.1.2.5" (partial := stronger-hyp) "仮定：原典の C に加え Mathlib IsLocallyPresentable C、局所小性と一つの colimit universe を明示し、生成射の類は小さい（Lean の形式的仮定が強い）。結論：I.rlp.llp と I.rlp の同じ functorial factorization があり、生成射の両端が κ-presentable なら指定分解の全 arrow factors が κ-filtered colimits を保つ。generatedLeft_le_of_closed と coproduct closure により左類は最小の弱飽和類に入り、原典の二結論に一致。この Mathlib presentability と原典の poset 型定義の完全な比較は含まない。"] _root_.SerrePositivity.Smith.AccessibleSmallObject.exists_factorization_at
