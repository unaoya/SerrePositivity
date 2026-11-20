module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingEdges

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 包含の実頂点の像を同型で閉じた本質像。 -/
def essentialImage {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) : Set (B.obj _⦋0⦌) :=
  {b | ∃ a : A.obj _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (i.hom.app (Opposite.op ⦋0⦌) a) b)}

lemma image_mem_essentialImage {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (a : A.obj _⦋0⦌) : i.hom.app (Opposite.op ⦋0⦌) a ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i :=
  ⟨a, ⟨Iso.refl _⟩⟩

/-- Verdier 列の条件。核の一致と商の普遍性の双方を含む。 -/
structure IsVerdierSequence {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : Prop where
  fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i.hom
  kernel (b : B.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) b) ↔ b ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i
  quotient : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i))

/-- 抽象 Verdier 列の対象と二つの完全関手。 -/
structure VerdierSequence where
  left : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}
  middle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}
  right : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}
  inclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap left middle
  projection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap middle right
  isVerdier : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence inclusion projection

namespace IsVerdierSequence

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 商は包含の全対象を零化する。 -/
lemma kills_inclusion (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (a : A.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((i.hom ≫ q.hom).app (Opposite.op ⦋0⦌) a) :=
  (h.kernel _).2 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.image_mem_essentialImage i a)

/-- 核の条件だけからも指定 cofiber 辺の反転が従う。 -/
lemma inverts (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.inverts_cofiberLocalizingEdges_of_kills q.hom _ (fun b hb ↦ (h.kernel b).2 hb)

/-- 各 quasicategory を標的とする実際の関手 ∞ 圏での商の普遍性。 -/
lemma universal (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (E : SSet.{u}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition q.hom
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)) h.inverts E) := by
  obtain ⟨hq, hE⟩ := h.quotient
  exact hE E

end IsVerdierSequence

/-- 完全関手が包含を零化することと、指定 cofiber 辺の反転は同値。 -/
theorem inverts_iff_kills_inclusion {A B E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)) ↔
      ∀ a : A.obj _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((i.hom ≫ F.hom).app (Opposite.op ⦋0⦌) a) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.inverts_cofiberLocalizingEdges_iff_kills]
  constructor
  · intro h a
    exact h _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.image_mem_essentialImage i a)
  · intro h b hb
    obtain ⟨a, ⟨e⟩⟩ := hb
    exact (h a).of_vertexIso (e.map F.hom)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
