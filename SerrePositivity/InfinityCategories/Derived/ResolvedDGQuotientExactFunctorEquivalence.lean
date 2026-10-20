module
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientExactDescent
/-!
概要：平坦分解後の商の全完全関手 ∞ 圏を、元の全零化完全関手 ∞ 圏と同定する。
方針：全局所化の充満忠実性と、平坦模型を通る完全性反映を使う。
規約：元の Hom の平坦性を仮定しない。使われ方：一般の dg Verdier 商。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 指定対象を零化する全完全関手 ∞ 圏への、平坦分解後の実商による前合成。 -/
def resolvedDGVerdierExactPrecomposition (P : Set D) (Y : SSet.{max u v}) :
    (exactFunctors (resolvedDGQuotientNerve A D P) Y : SSet.{max u v}) ⟶
      (zeroingExactFunctors (dgNerve A D) Y (Simplex.vertex '' P) : SSet.{max u v}) := by
  let := resolvedDGQuotientFunctor_isExactFunctor A D P
  exact zeroingExactPrecomposition (resolvedDGQuotientFunctor A D P) (Simplex.vertex '' P)
    (by rintro _ ⟨x, hx, rfl⟩; exact resolvedDGQuotientFunctor_kills A D P ⟨x, hx⟩) Y
/-- 任意の安定標的について、一般の実 dg 商の全完全関手圏は全零化完全関手圏と同値。 -/
theorem resolvedDGVerdierExactPrecomposition_isQCatEquivalence (P : Set D)
    (Y : SSet.{max u v}) [Quasicategory Y] [IsStable Y] :
    IsQCatEquivalence (resolvedDGVerdierExactPrecomposition A D P Y) := by
  let := resolvedDGQuotientFunctor_isExactFunctor A D P
  apply zeroingExactPrecomposition_isQCatEquivalence
    (resolvedDGQuotientFunctor A D P) (Simplex.vertex '' P)
    (by rintro _ ⟨x, hx, rfl⟩; exact resolvedDGQuotientFunctor_kills A D P ⟨x, hx⟩)
  · exact resolvedDGQuotientPrecomposition_isFullyFaithful A D P Y
  · intro F hF hkill
    exact resolvedDGVerdierExactFunctor_extension_exists A D P F
      (fun b => hkill _ ⟨b.val, b.property, rfl⟩)
end SerrePositivity.InfinityCategories
