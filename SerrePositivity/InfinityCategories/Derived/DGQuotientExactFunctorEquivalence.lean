module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientExactDescent
public import SerrePositivity.InfinityCategories.Derived.ExactFunctorCategoryEquivalence
/-!
概要：Drinfeld 商の完全関手 ∞ 圏を、元の零化完全関手 ∞ 圏と同定する。
方針：全関手圏の局所化の充満忠実性と、完全性を反映する実辺表示を使う。
規約：全自然変換を保持。使われ方：安定 Verdier 列の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve MonoidalClosed SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 商の前合成は、反転関手への因子化を忘れた元の全関手圏でも充満忠実。 -/
lemma dgQuotientPrecomposition_isFullyFaithful (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (Y : SSet.{max u v}) [Quasicategory Y] :
    IsFullyFaithful ((pre (dgQuotientNerveProjection A D P)).app Y) := by
  have hf := dgVerdierLocalizationPrecomposition_isFullyFaithful A D P hP Y
  have hi := isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom (dgNerve A D)).obj Y)
    (IsInvertingFunctorVertex (dgNerve A D) Y (dgVerdierEdges A D P))
  change IsFullyFaithful (invertingFunctors (dgNerve A D) Y (dgVerdierEdges A D P)).ι at hi
  have hh := hf.comp hi
  rw [localizationPrecomposition_ι] at hh
  exact hh
/-- 零化完全関手圏への、実商射影による前合成。 -/
def dgVerdierExactPrecomposition (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (Y : SSet.{max u v}) : (exactFunctors (dgQuotientNerve A D P) Y : SSet.{max u v}) ⟶
      (zeroingExactFunctors (dgNerve A D) Y (Simplex.vertex '' P) : SSet.{max u v}) := by
  let := dgQuotientNerveProjection_isExactFunctor A D P hP
  exact zeroingExactPrecomposition (dgQuotientNerveProjection A D P) (Simplex.vertex '' P)
    (by rintro _ ⟨x, hx, rfl⟩; exact dgQuotientNerveProjection_kills A D P ⟨x, hx⟩) Y
/-- 任意の安定標的について、商の全完全関手圏は元の全零化完全関手圏と同値。 -/
lemma dgVerdierExactPrecomposition_isQCatEquivalence (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (Y : SSet.{max u v}) [Quasicategory Y] [IsStable Y] :
    IsQCatEquivalence (dgVerdierExactPrecomposition A D P hP Y) := by
  let := dgQuotientNerveProjection_isExactFunctor A D P hP
  apply zeroingExactPrecomposition_isQCatEquivalence
    (dgQuotientNerveProjection A D P) (Simplex.vertex '' P)
    (by rintro _ ⟨x, hx, rfl⟩; exact dgQuotientNerveProjection_kills A D P ⟨x, hx⟩)
  · exact dgQuotientPrecomposition_isFullyFaithful A D P hP Y
  · intro F hF hkill
    exact dgVerdierExactFunctor_extension_exists A D P hP F
      (fun b => hkill _ ⟨b.val, b.property, rfl⟩)
end SerrePositivity.InfinityCategories
