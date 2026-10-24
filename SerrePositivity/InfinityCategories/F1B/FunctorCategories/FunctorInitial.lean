module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorRelativeInitial

/-!
概要：関手単体集合の点ごとの始対象性。
方針：終対象への射の上の相対始点境界充填を使い、標的条件を一意性で消去する。
規約：関手の標的の quasicategory 性は不要。
使われ方：Kerodon Corollary 7.1.8.15 の空図式の場合、始対象による弱可縮性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：各頂点で始対象となる関手は関手単体集合でも始対象。
方針：点ごとの相対境界充填を内部 Hom に移し、一意な終対象への図式で検査する。
規約：K と X は任意の単体集合。
使われ方：Kerodon Corollary 7.1.8.15 の空図式の場合。 -/
lemma isInitialVertex_functorVertex_of_pointwise {K X : SSet.{u}} (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, IsInitialVertex (f.app (Opposite.op ⦋0⦌) k)) :
    IsInitialVertex (functorVertex f) := by
  have ht : ∀ k : K _⦋0⦌,
      InitialBoundaryLifting (terminal.from X) (f.app (Opposite.op ⦋0⦌) k) := by
    intro k n a b ha sq
    obtain ⟨F, hF⟩ := hf k n a ha
    exact ⟨F, hF, terminal.hom_ext _ _⟩
  have h := initialBoundaryLifting_ihom_of_pointwise (terminal.from X) f ht
  intro n a ha
  let b : (Δ[n + 1] : SSet.{u}) ⟶ (ihom K).obj (⊤_ SSet.{u}) :=
    curry (terminal.from (K ⊗ (Δ[n + 1] : SSet.{u})))
  have sq : CommSq a (boundary (n + 1)).ι ((ihom K).map (terminal.from X)) b := by
    constructor
    apply uncurry_injective
    exact terminal.hom_ext _ _
  obtain ⟨F, hF, _⟩ := h n a b ha sq
  exact ⟨F, hF⟩

end SerrePositivity.InfinityCategories
