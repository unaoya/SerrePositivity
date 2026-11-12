module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：錐族の形状の制限は底の図式の制限と可換で、比較円柱の固定条件も保つ。
方針：join の右包含の自然性に内部 Hom の前合成を適用する。
規約：元の全円柱を制限。使われ方：大きい部分形状から共通境界への比較三角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の錐族の形状の制限は、元の底の図式の制限と厳密に可換。 -/
lemma coneFamilyReindex_restriction {J K X : SSet.{u}} (i : J ⟶ K) :
    (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) i)).app X ≫ coneRestriction J X =
      coneRestriction K X ≫ (pre i).app X := by
  have h := congrArg (fun q => (pre q).app X) (joinInr_joinMap (𝟙 (Δ[0] : SSet.{u})) i)
  simpa only [coneRestriction, pre_map, NatTrans.comp_app] using h

/-- 底を固定する元の比較円柱を部分形状へ制限しても、制限された底は全時刻で固定。 -/
lemma limitConeFamilyComparison_reindex {B J K X : SSet.{u}} (i : J ⟶ K)
    {f g : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X} (H : SSet.Homotopy f g)
    (a : B ⟶ (ihom K).obj X)
    (hH : H.h ≫ coneRestriction K X = fst B (Δ[1] : SSet.{u}) ≫ a) :
    (functorHomotopyPostcomp H ((pre (joinMap (𝟙 (Δ[0] : SSet.{u})) i)).app X)).h ≫
      coneRestriction J X = fst B (Δ[1] : SSet.{u}) ≫ (a ≫ (pre i).app X) := by
  change (H.h ≫ (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) i)).app X) ≫
    coneRestriction J X = _
  rw [Category.assoc, coneFamilyReindex_restriction, ← Category.assoc, hH, Category.assoc]

end SerrePositivity.InfinityCategories.F2
