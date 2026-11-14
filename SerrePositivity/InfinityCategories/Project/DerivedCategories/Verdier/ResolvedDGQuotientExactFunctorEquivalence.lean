module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientExactDescent
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 指定対象を零化する全完全関手 ∞ 圏への、平坦分解後の実商による前合成。 -/
def resolvedDGVerdierExactPrecomposition (P : Set D) (Y : SSet.{max u v}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactFunctors (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve A D P) Y : SSet.{max u v}) ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactFunctors (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) Y (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) : SSet.{max u v}) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isExactFunctor A D P
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)
    (by rintro _ ⟨x, hx, rfl⟩; exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_kills A D P ⟨x, hx⟩) Y
/-- 任意の安定標的について、一般の実 dg 商の全完全関手圏は全零化完全関手圏と同値。 -/
theorem resolvedDGVerdierExactPrecomposition_isQCatEquivalence (P : Set D)
    (Y : SSet.{max u v}) [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (resolvedDGVerdierExactPrecomposition A D P Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isExactFunctor A D P
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)
    (by rintro _ ⟨x, hx, rfl⟩; exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_kills A D P ⟨x, hx⟩)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientPrecomposition_isFullyFaithful A D P Y
  · intro F hF hkill
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGVerdierExactFunctor_extension_exists A D P F
      (fun b => hkill _ ⟨b.val, b.property, rfl⟩)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
