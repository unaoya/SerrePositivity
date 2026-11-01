module

public import SerrePositivity.InfinityCategories.F1B.Localization.AdjointLocalization
public import SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence

/-!
概要：完全な反射射影とその核を表す充満忠実な包含は Verdier 列を与える。
方針：射影が反転する辺を核に cofiber を持つ辺に同定し、随伴からの局所化を使う。
規約：商の普遍性を仮定に含めない。使われ方：K-8 の半直交分解の分裂列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma invertedEdges_eq_cofiber_kernel {A T B : StableCategory.{u}}
    (i : ExactMap A T) (q : ExactMap T B)
    (hk : ∀ x, IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x) ↔ x ∈ essentialImage i) :
    invertedEdges q.hom = cofiberLocalizingEdges (essentialImage i) := by
  ext e
  constructor
  · intro he
    let c := chosenCofiberSquare (edgeOfSimplex e)
    have hz := (c.map_isInvertible_iff_zero q.hom).1 he
    exact ⟨c, c.cofiber, (hk _).1 hz, ⟨Iso.refl _⟩⟩
  · intro he
    exact inverts_cofiberLocalizingEdges_of_kills q.hom _ (fun x hx => (hk x).2 hx) he

/-- 可逆余単位の随伴と核の同定から、実関手圏上の商の普遍性を導く。 -/
theorem isVerdierSequence_of_adjoint {A T B : StableCategory.{u}}
    (i : ExactMap A T) (q : ExactMap T B) (j : ExactMap B T)
    (hi : IsFullyFaithful i.hom)
    (hk : ∀ x, IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x) ↔ x ∈ essentialImage i)
    (a : QCatAdjunction q.hom j.hom) [IsIso a.counit] : IsVerdierSequence i q where
  fullyFaithful := hi
  kernel := hk
  quotient := by
    rw [← invertedEdges_eq_cofiber_kernel i q hk]
    exact AdjointLocalization.isLocalization a

end SerrePositivity.KST.LocalizingInvariants
