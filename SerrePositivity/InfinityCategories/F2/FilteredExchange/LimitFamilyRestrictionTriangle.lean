module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LimitConeFamilyTriangle
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LimitConeFamilyReindex

/-!
概要：大きい部分極限への比較と共通境界の極限への指定比較を、同じ対角辺で結ぶ。
方針：大きい錐族を制限し、共通境界の極限へ比較した上で指定三辺を充填する。
規約：元の対角円柱を保持。使われ方：形状の貼り合わせの二脚の共通長辺の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B J K X : SSet.{u}} [Quasicategory X] (i : J ⟶ K)
local notation "R" => NatTrans.app (pre (joinMap (𝟙 Δ[0]) i)) X

/-- 部分極限の指定比較と元の対角円柱を保つ、共通境界の極限への比較三角形が存在。 -/
lemma exists_limitFamilyRestrictionTriangle
    (f q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X)
    (r : B ⟶ (ihom (join (Δ[0] : SSet.{u}) J)).obj X)
    (hfq : f ≫ coneRestriction K X = q ≫ coneRestriction K X)
    (hfr : (f ≫ R) ≫ coneRestriction J X = r ≫ coneRestriction J X)
    (hr : ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (r.app (Opposite.op ⦋0⦌) b)))
    (H : SSet.Homotopy f q)
    (hH : H.h ≫ coneRestriction K X = fst B (Δ[1] : SSet.{u}) ≫ (f ≫ coneRestriction K X))
    (D : SSet.Homotopy (f ≫ R) r)
    (hD : D.h ≫ coneRestriction J X = fst B (Δ[1] : SSet.{u}) ≫
      ((f ≫ R) ≫ coneRestriction J X)) :
    ∃ U : SSet.Homotopy (q ≫ R) r,
      U.h ≫ coneRestriction J X = fst B (Δ[1] : SSet.{u}) ≫
        ((f ≫ R) ≫ coneRestriction J X) ∧
      Nonempty {T : FunctorCompositionTriangle (functorHomotopyPostcomp H R) U D //
        T.diagram ≫ (ihom B).map (coneRestriction J X) =
          SSet.const (functorVertex ((f ≫ R) ≫ coneRestriction J X))} := by
  have hs (s : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X) :
      (s ≫ R) ≫ coneRestriction J X = (s ≫ coneRestriction K X) ≫ (pre i).app X := by
    rw [Category.assoc, coneFamilyReindex_restriction, ← Category.assoc]
  have hq : (q ≫ R) ≫ coneRestriction J X = (f ≫ R) ≫ coneRestriction J X := by
    rw [hs q, hs f, hfq]
  obtain ⟨U, hU⟩ := exists_limitConeFamilyComparison (q ≫ R) r (hq.trans hfr) hr
  rw [hq] at hU
  have hL := limitConeFamilyComparison_reindex i H (f ≫ coneRestriction K X) hH
  rw [← hs f] at hL
  exact ⟨U, hU, limitConeFamilyComparisonTriangle _ hr
    (functorHomotopyPostcomp H R) U D hL hU hD⟩

end SerrePositivity.InfinityCategories.F2
