module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportRestrictedPrismComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberDataEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamilyNaturality

/-!
概要：元の輸送族の比較を初期係数で制限すると、同じ二輸送の初期値制限の比較となる。
方針：元の同じ実二 prism へ戻し、底・初期値の表示だけを合わせる。
規約：元の指定 endpointIso を保持。使われ方：元の初期値 q に沿う比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定比較の初期係数制限は、同じ元の二輸送の初期値制限の指定比較。 -/
lemma fiberTransportFamily_endpointIso_precomposeSource {E B K K' L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) (r : K' ⟶ K) :
    (T.endpointIso p f γ h₁ U).precomp (r ▷ L) =
      (T.precomposeSource r).endpointIso p (r ≫ f) γ h₁ (U.precomposeSource r) := by
  calc
    _ = fiberTransportRestrictedPrismComparison p f γ h₁ T U (r ▷ L) :=
      (fiberTransportRestrictedPrismComparison_eq_endpointIso p f γ h₁ T U (r ▷ L)).symm
    _ = fiberTransportFamilyPrismComparison p (r ≫ f) γ h₁
        (T.precomposeSource r) (U.precomposeSource r) := by
      unfold fiberTransportRestrictedPrismComparison fiberTransportFamilyPrismComparison
      apply relativeExtensionFiberEndpoint_witnessIso_eq_of_dataEq
      · rw [← whiskerLeft_comp_assoc, whiskerRight_snd]
      · simp only [← Category.assoc]
        rw [whiskerRight_fst]
      · rfl
      · rfl
    _ = _ := fiberTransportFamilyPrismComparison_eq_endpointIso p (r ≫ f) γ h₁
      (T.precomposeSource r) (U.precomposeSource r)

end SerrePositivity.InfinityCategories.F2
