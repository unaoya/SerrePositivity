module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.LimitConeFamilyReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeRestrictionCocartesianEdge

/-!
概要：部分形状への錐族の制限は、元の頂点関手と頂点上の比較円柱を変えない。
方針：join の左包含の自然性と元の頂点評価を照合する。
規約：頂点の等号は射全体の等号。使われ方：二部分の比較三角形の共通頂点の固定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の形状の制限は、元の錐の頂点での評価を厳密に保つ。 -/
lemma coneFamilyReindex_apex {J K X : SSet.{u}} (i : J ⟶ K) :
    (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) i)).app X ≫ coneApexEvaluation J X =
      coneApexEvaluation K X := by
  have hm : joinInl (Δ[0] : SSet.{u}) J ≫ joinMap (𝟙 Δ[0]) i = joinInl Δ[0] K := by
    rw [joinInl_joinMap, Category.id_comp]
  have hk := ConcreteCategory.congr_hom (NatTrans.congr_app hm (Opposite.op ⦋0⦌))
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  unfold coneApexEvaluation
  rw [functorCoconePrecomp_evaluate]
  exact congrArg (fun v => evaluateFunctorAt (Y := X) v) hk

/-- 元の錐族を制限しても、元の頂点関手は同じ射。 -/
lemma limitConeFamily_reindex_apex {B J K X : SSet.{u}} (i : J ⟶ K)
    (f : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X) :
    (f ≫ (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) i)).app X) ≫ coneApexEvaluation J X =
      f ≫ coneApexEvaluation K X := by
  rw [Category.assoc, coneFamilyReindex_apex]

/-- 元の比較円柱を制限しても、頂点で評価した円柱全体は厳密に一致する。 -/
lemma limitFamilyRestrictionComparison_apex {B J K X : SSet.{u}} (i : J ⟶ K)
    {f g : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X} (H : SSet.Homotopy f g) :
    (functorHomotopyPostcomp (functorHomotopyPostcomp H
      ((pre (joinMap (𝟙 (Δ[0] : SSet.{u})) i)).app X)) (coneApexEvaluation J X)).h =
        (functorHomotopyPostcomp H (coneApexEvaluation K X)).h := by
  change (H.h ≫ (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) i)).app X) ≫
    coneApexEvaluation J X = _
  rw [Category.assoc, coneFamilyReindex_apex]
  rfl

end SerrePositivity.InfinityCategories.F2
