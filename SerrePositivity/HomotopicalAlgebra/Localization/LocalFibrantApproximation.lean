module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic

public import SerrePositivity.HomotopicalAlgebra.Localization.LocalBoundaryGenerators
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleGeneratedPair
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFactorization

/-! # An actual accessible cofibration into a fibrant local object

The small generator family combines the original generating trivial
cofibrations with the relative latching generators. The small-object
argument constructs an accessible functor and a natural cofibration into
local fibrant objects. Local-equivalence of that cofibration is not yet
asserted; it is a separate necessary step toward localization existence.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield.LocalFibrantApproximation
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (S : MorphismProperty C)

abbrev generators : MorphismProperty C := J ⊔ LocalBoundaryGenerators.generators cof S

omit [IsLocallyPresentable.{w} C] in
include I in
lemma original_generators_isSmall : J.IsSmall.{w} := by
  obtain ⟨κ, hκ, hb, hJ⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := J)
  exact SmallObject.isSmall J κ

omit [IsLocallyPresentable.{w} C] in
include I in
lemma generators_isSmall [S.IsSmall.{w}] : (generators J cof S).IsSmall.{w} := by
  have := original_generators_isSmall I J
  let T : Bool → MorphismProperty C := fun b =>
    if b then J else LocalBoundaryGenerators.generators cof S
  have : ∀ b, (T b).IsSmall.{w} := by
    intro b
    cases b <;> dsimp [T] <;> infer_instance
  have he : (⨆ b, T b) = generators J cof S := by simp [iSup_bool_eq, T, generators]
  rw [← he]
  infer_instance

omit [IsLocallyPresentable.{w} C] in
include I in
lemma generators_le_cofibrations : generators J cof S ≤ cofibrations C := by
  apply sup_le
  · intro X Y f hf
    have ht : trivialCofibrations C f :=
      (J.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J).symm.le) f hf
    exact ht.1
  · exact LocalBoundaryGenerators.generators_le_cofibrations cof S

omit [IsLocallyPresentable.{w} C] in
include I in
lemma generated_left_le_cofibrations : (generators J cof S).rlp.llp ≤ cofibrations C := by
  have he : (trivialFibrations C).llp = cofibrations C := trivialFibrations_llp C
  have h : generators J cof S ≤ (trivialFibrations C).llp :=
    (generators_le_cofibrations I J cof S).trans he.symm.le
  have hr : trivialFibrations C ≤ (generators J cof S).rlp :=
    (MorphismProperty.le_llp_iff_le_rlp _ _).mp h
  exact (MorphismProperty.antitone_llp hr).trans he.le

omit [IsLocallyPresentable.{w} C] in
include I in
lemma right_le_fibrations : (generators J cof S).rlp ≤ fibrations C := by
  have h : (generators J cof S).rlp ≤ J.rlp := MorphismProperty.antitone_rlp le_sup_left
  exact h.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_J (I := I) (J := J)).le

variable [ModelCategory SSet.{v}]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

omit [IsLocallyPresentable.{w} C] in
include I hcof in
lemma localFibrant_of_rlp (Y : C) (hY : (generators J cof S).rlp (terminal.from Y)) :
    localFibrantObjects cof fib S Y := by
  have : Fibration (terminal.from Y) := ⟨right_le_fibrations I J cof S _ hY⟩
  have : IsFibrant Y := (isFibrant_iff Y).mpr inferInstance
  have hb : (LocalBoundaryGenerators.generators cof S).rlp (terminal.from Y) :=
    MorphismProperty.antitone_rlp le_sup_right _ hY
  exact ⟨inferInstance, LocalBoundaryGenerators.localObjects_of_rlp cof S hcof fib Y hb⟩

include I hcof in
lemma exists_accessible_approximation [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : MorphismProperty.FunctorialFactorizationData
          (generators J cof S).rlp.llp (generators J cof S).rlp,
        d.Z.IsCardinalAccessible κ ∧
        (Smith.AccessibleFactorization.terminalRestriction d).IsCardinalAccessible κ ∧
        (∀ X, cofibrations C ((Smith.AccessibleFactorization.terminalComparison d).app X)) ∧
        ∀ X, localFibrantObjects cof fib S
          ((Smith.AccessibleFactorization.terminalRestriction d).obj X) := by
  have := generators_isSmall I J cof S
  obtain ⟨κ, hκ, d, _, hd, _⟩ :=
    Smith.exists_common_accessible_generated_factorizations
      (generators J cof S) (generators J cof S)
  have := hd
  have := Smith.locallyPresentable_hasColimits (C := C)
  refine ⟨κ, hκ, d, hd, Smith.AccessibleFactorization.terminalRestriction_isCardinalAccessible d κ,
    fun X => generated_left_le_cofibrations I J cof S _
      (Smith.AccessibleFactorization.terminalComparison_mem d X), ?_⟩
  intro X
  let R := Smith.AccessibleFactorization.terminalRestriction d
  have he : d.p.app (Arrow.mk (terminal.from X)) = terminal.from (R.obj X) := terminal.hom_ext _ _
  apply localFibrant_of_rlp I J cof S fib hcof (R.obj X)
  exact he ▸ d.hp (Arrow.mk (terminal.from X))

end SerrePositivity.Bousfield.LocalFibrantApproximation
