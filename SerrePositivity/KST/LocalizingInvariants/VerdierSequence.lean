module

public import SerrePositivity.KST.LocalizingInvariants.StableCategories
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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

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

end SerrePositivity.KST.LocalizingInvariants
