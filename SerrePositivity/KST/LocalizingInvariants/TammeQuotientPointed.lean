module

public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientDetection
public import SerrePositivity.KST.LocalizingInvariants.LocalizationZeroPreservation

/-!
概要：一般商候補は実零対象を持ち、元の射影の核は通常 pullback の本質像と一致する。
方針：局所化の零対象保存と、零対象の像との実同型による対象検出を接続する。
規約：安定性・完全性は後続。使われ方：一般の Verdier 列の核の実証。
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
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma tammeQuotientMap_preservesZero : PreservesZeroVertices (tammeQuotientMap p q) :=
  localization_preservesZero _ _ (tammeQuotient_isLocalization p q)

lemma tammeQuotient_zeroImage_isZero : IsZeroVertex
    ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌)
      (chosenZeroVertex (laxCategory p q).obj).vertex) :=
  tammeQuotientMap_preservesZero p q _ (chosenZeroVertex (laxCategory p q).obj).isZero

instance tammeQuotient_hasZeroVertex : HasZeroVertex (tammeQuotient p q) :=
  ⟨⟨_, tammeQuotient_zeroImage_isZero p q⟩⟩

/-- 商内の真の零対象性と、元の通常 pullback の本質像の一致。 -/
lemma tammeQuotientMap_kernel (x : (laxCategory p q).obj _⦋0⦌) :
    IsZeroVertex ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) x) ↔
      x ∈ essentialImage (pullbackInclusion p q) := by
  rw [← tammeQuotient_zeroImageIso_iff_essentialImage]
  constructor
  · intro hx
    exact ⟨terminalVertexIso (tammeQuotient_zeroImage_isZero p q).2 hx.2⟩
  · rintro ⟨e⟩
    exact (tammeQuotient_zeroImage_isZero p q).of_vertexIso e

end SerrePositivity.KST.LocalizingInvariants
