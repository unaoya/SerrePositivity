module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-! # Uniform presentability and small-object arguments for Smith recognition

The generating class is small in the colimit universe. No model structure is
assumed. A single regular cardinal bounds both endpoints of all generators.
-/

@[expose] public section
universe w t v u
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.Smith

variable {C : Type u} [Category.{v} C]

/-- A small family of presentable objects admits one regular presentability cardinal. -/
lemma exists_common_presentability {ι : Type t} [Small.{w} ι] (a : ι → C)
    [∀ i, IsPresentable.{w} (a i)] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), ∀ i, IsCardinalPresentable (a i) κ := by
  choose κ hreg hp using fun i ↦
    Functor.IsAccessible.exists_cardinal (coyoneda.obj (op (a i)))
  obtain ⟨κ', hκ', bounds⟩ :=
    HasCardinalLT.exists_regular_cardinal_forall (fun i ↦ (κ i).ord.ToType)
  let : Fact κ'.IsRegular := ⟨hκ'⟩
  refine ⟨κ', inferInstance, fun i ↦ ?_⟩
  have h := bounds i
  simp only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_toType, Cardinal.card_ord] at h
  exact isCardinalPresentable_monotone C h.le _ (hp i)

/-- Uniformity includes codomains, even though the small-object argument only uses domains. -/
lemma exists_common_arrow_presentability [IsAccessibleCategory.{w} C]
    {ι : Type t} [Small.{w} ι] (a : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∀ i, IsCardinalPresentable (a i).left κ ∧ IsCardinalPresentable (a i).right κ := by
  let b : Sum ι ι → C := Sum.elim (fun i ↦ (a i).left) (fun i ↦ (a i).right)
  obtain ⟨κ, hκ, hb⟩ := exists_common_presentability b
  exact ⟨κ, hκ, fun i ↦ ⟨hb (.inl i), hb (.inr i)⟩⟩

/-- Extract the colimits at the universe used by local presentability. -/
lemma locallyPresentable_hasColimits [IsLocallyPresentable.{w} C] :
    HasColimitsOfSize.{w, w} C := by
  obtain ⟨κ, hκ, hC⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  exact inferInstance

/-- A small class in a locally presentable category permits the actual Mathlib SOA.
This is a theorem rather than an instance, avoiding a cycle with SOA-to-smallness APIs. -/
lemma hasSmallObjectArgument [IsLocallyPresentable.{w} C]
    (I : MorphismProperty C) [I.IsSmall.{w}] : I.HasSmallObjectArgument.{w} := by
  let := locallyPresentable_hasColimits (C := C)
  obtain ⟨κ, hκ, hb⟩ := exists_common_arrow_presentability (fun i : I.toSet ↦ i.val)
  let : Fact κ.IsRegular := hκ
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType hκ.out.ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have : I.IsCardinalForSmallObjectArgument κ := by
    refine { preservesColimit := ?_ }
    intro A B X Y f hf g hg
    have : IsCardinalPresentable A κ := (hb ⟨Arrow.mk f, hf⟩).1
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (coyoneda.obj (op A)) κ κ.ord.ToType
    infer_instance
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

end SerrePositivity.Smith
