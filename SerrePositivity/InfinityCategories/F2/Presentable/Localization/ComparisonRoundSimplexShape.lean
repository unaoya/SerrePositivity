module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonRoundRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.DoubleConeSimplexShape

/-!
概要：一巡の全比較形状を二次数先の標準単体へ正規化する。
方針：元の形状同型を二つの join へ送り、前置包含の自然性を使う。
規約：元の指定包含を保持する。使われ方：可算全図式の標準単体列への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
  {hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i))}
  {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}

/-- 一巡前の形状同型は、一巡後の二次数先への同型へ延びる。 -/
def ComparisonRound.simplexShapeIso (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    {n : ℕ} (e : s.shape ≅ (Δ[n] : SSet.{u})) :
    (r.next hD₁).shape ≅ (Δ[n + 2] : SSet.{u}) :=
  joinIso (joinIso e (Iso.refl _)) (Iso.refl _) ≪≫ doubleConeSimplexIso n

/-- 一巡の元の指定包含は、正規化の後で同じ全前置標準単体となる。 -/
lemma ComparisonRound.simplexShapeIso_prefix (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    {n : ℕ} (e : s.shape ≅ (Δ[n] : SSet.{u})) :
    r.inclusion hD₁ ≫ (r.simplexShapeIso hD₁ e).hom =
      e.hom ≫ simplexPrefix (by omega : n ≤ n + 2) := by
  dsimp only [ComparisonRound.inclusion, ComparisonRound.simplexShapeIso,
    Iso.trans_hom, joinIso, Iso.refl_hom]
  simp only [Category.assoc]
  rw [joinInl_joinMap_assoc, joinInl_joinMap_assoc, doubleConeSimplexIso_prefix]

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
