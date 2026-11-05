module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingEdges

/-!
概要：充満忠実な完全包含と、その像を核とする Verdier 商。
方針：cofiber が包含の本質像に属する辺に関する局所化普遍性を明記する。
規約：商の存在は主張しない。使われ方：D の Drinfeld 商との後続の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence
end SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence
namespace SerrePositivity.InfinityCategories.Stable.Verdier
open SerrePositivity.KST.LocalizingInvariants

/-- 包含の実頂点の像を同型で閉じた本質像。 -/
def essentialImage {A B : StableCategory.{u}} (i : ExactMap A B) : Set (B.obj _⦋0⦌) :=
  {b | ∃ a : A.obj _⦋0⦌, Nonempty (VertexIso (i.hom.app (Opposite.op ⦋0⦌) a) b)}

lemma image_mem_essentialImage {A B : StableCategory.{u}} (i : ExactMap A B)
    (a : A.obj _⦋0⦌) : i.hom.app (Opposite.op ⦋0⦌) a ∈ essentialImage i :=
  ⟨a, ⟨Iso.refl _⟩⟩

/-- Verdier 列の条件。核の一致と商の普遍性の双方を含む。 -/
structure IsVerdierSequence {A B C : StableCategory.{u}}
    (i : ExactMap A B) (q : ExactMap B C) : Prop where
  fullyFaithful : IsFullyFaithful i.hom
  kernel (b : B.obj _⦋0⦌) :
    IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) b) ↔ b ∈ essentialImage i
  quotient : IsLocalization q.hom (cofiberLocalizingEdges (essentialImage i))

/-- 抽象 Verdier 列の対象と二つの完全関手。 -/
structure VerdierSequence where
  left : StableCategory.{u}
  middle : StableCategory.{u}
  right : StableCategory.{u}
  inclusion : ExactMap left middle
  projection : ExactMap middle right
  isVerdier : IsVerdierSequence inclusion projection

namespace IsVerdierSequence
open SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

/-- 商は包含の全対象を零化する。 -/
lemma kills_inclusion (h : IsVerdierSequence i q) (a : A.obj _⦋0⦌) :
    IsZeroVertex ((i.hom ≫ q.hom).app (Opposite.op ⦋0⦌) a) :=
  (h.kernel _).2 (image_mem_essentialImage i a)

/-- 核の条件だけからも指定 cofiber 辺の反転が従う。 -/
lemma inverts (h : IsVerdierSequence i q) :
    InvertsEdges q.hom (cofiberLocalizingEdges (essentialImage i)) :=
  inverts_cofiberLocalizingEdges_of_kills q.hom _ (fun b hb ↦ (h.kernel b).2 hb)

/-- 各 quasicategory を標的とする実際の関手 ∞ 圏での商の普遍性。 -/
lemma universal (h : IsVerdierSequence i q) (E : SSet.{u}) [Quasicategory E] :
    IsQCatEquivalence (localizationPrecomposition q.hom
      (cofiberLocalizingEdges (essentialImage i)) h.inverts E) := by
  obtain ⟨hq, hE⟩ := h.quotient
  exact hE E

end IsVerdierSequence

/-- 完全関手が包含を零化することと、指定 cofiber 辺の反転は同値。 -/
theorem inverts_iff_kills_inclusion {A B E : StableCategory.{u}}
    (i : ExactMap A B) (F : ExactMap B E) :
    InvertsEdges F.hom (cofiberLocalizingEdges (essentialImage i)) ↔
      ∀ a : A.obj _⦋0⦌,
        IsZeroVertex ((i.hom ≫ F.hom).app (Opposite.op ⦋0⦌) a) := by
  rw [inverts_cofiberLocalizingEdges_iff_kills]
  constructor
  · intro h a
    exact h _ (image_mem_essentialImage i a)
  · intro h b hb
    obtain ⟨a, ⟨e⟩⟩ := hb
    exact (h a).of_vertexIso (e.map F.hom)

end SerrePositivity.InfinityCategories.Stable.Verdier

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.essentialImage := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.image_mem_essentialImage := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.image_mem_essentialImage

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.inverts_iff_kills_inclusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.inverts_iff_kills_inclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.casesOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.fullyFaithful := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.fullyFaithful

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.inverts := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.inverts

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.kernel := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.kernel

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.kills_inclusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.kills_inclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.mk := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.mk

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.quotient := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.quotient

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.rec := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.universal := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.universal

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.inclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.inclusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.isVerdier := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.isVerdier

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.left (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.left := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.left

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.middle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.middle := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.middle

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.mk := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.projection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.projection := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.rec := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.right := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.right

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsVerdierSequence.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.mk._flat_ctor

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.mk.sizeOf_spec
