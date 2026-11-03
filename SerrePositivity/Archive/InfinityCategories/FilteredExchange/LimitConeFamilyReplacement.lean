module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.LimitConeFamilyComparison

/-!
概要：元の錐族を同じ図式上の極限錐族で置換し、指定された比較円柱を付ける。
方針：元の制限図式の各点の極限から coherent な族を構成し、元の底の上で比較する。
規約：元の族は比較円柱の始点として保持。使われ方：部分形状の極限への比較の組み立て。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の錐族を同じ図式の極限錐族へ置換し、底を厳密に保つ比較円柱を構成できる。 -/
lemma exists_limitConeFamilyReplacement {B K X : SSet.{u}} [Quasicategory X]
    (f : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X)
    (hp : ∀ b : B _⦋0⦌, HasLimit
      (joinInr Δ[0] K ≫ functorVertexConeMap (f.app (Opposite.op ⦋0⦌) b))) :
    ∃ q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X,
      q ≫ coneRestriction K X = f ≫ coneRestriction K X ∧
      (∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (q.app (Opposite.op ⦋0⦌) b))) ∧
      ∃ H : SSet.Homotopy f q,
        H.h ≫ coneRestriction K X = fst B (Δ[1] : SSet.{u}) ≫ (f ≫ coneRestriction K X) := by
  have hr : ∀ b : B _⦋0⦌, HasLimit ((functorVertexEquiv K X).symm
      ((f ≫ coneRestriction K X).app (Opposite.op ⦋0⦌) b)) := by
    intro b
    change HasLimit ((functorVertexEquiv K X).symm
      (((pre (joinInr Δ[0] K)).app X).app (Opposite.op ⦋0⦌)
        (f.app (Opposite.op ⦋0⦌) b)))
    rw [functorVertexMap_precomp]
    exact hp b
  obtain ⟨q, hq, hlim⟩ := exists_pointwiseLimitConeFamily (f ≫ coneRestriction K X) hr
  exact ⟨q, hq, hlim, exists_limitConeFamilyComparison f q hq.symm hlim⟩

end SerrePositivity.InfinityCategories.F2
