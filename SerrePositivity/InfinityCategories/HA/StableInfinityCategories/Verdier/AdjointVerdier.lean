module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.AdjointLocalization
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma invertedEdges_eq_cofiber_kernel {A T B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A T) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap T B)
    (hk : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x) ↔ x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges q.hom = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) := by
  ext e
  constructor
  · intro he
    let c := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e)
    have hz := (c.map_isInvertible_iff_zero q.hom).1 he
    exact ⟨c, c.cofiber, (hk _).1 hz, ⟨Iso.refl _⟩⟩
  · intro he
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.inverts_cofiberLocalizingEdges_of_kills q.hom _ (fun x hx => (hk x).2 hx) he

/-- 可逆余単位の随伴と核の同定から、実関手圏上の商の普遍性を導く。 -/
theorem isVerdierSequence_of_adjoint {A T B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A T) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap T B) (j : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B T)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i.hom)
    (hk : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x) ↔ x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom j.hom) [IsIso a.counit] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q where
  fullyFaithful := hi
  kernel := hk
  quotient := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.invertedEdges_eq_cofiber_kernel i q hk]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization a

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.invertedEdges_eq_cofiber_kernel := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.invertedEdges_eq_cofiber_kernel

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.isVerdierSequence_of_adjoint := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.isVerdierSequence_of_adjoint
