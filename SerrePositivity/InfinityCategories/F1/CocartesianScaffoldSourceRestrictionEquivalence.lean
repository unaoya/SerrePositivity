module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldStandardSourceFactorization
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldBridgeCoreRestriction

/-!
概要：全次元で、元の全 Hom の最初の辺と尾部への同じ制限は自明 Kan。
方針：同じ小さい表示への native core 制限の自明 Kan 性を表示同型で移す。
規約：元の全相対 Hom と同じ制限写像を保持する。
使われ方：元の分類 Hom 作用の全単体への帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin (n + 2)))))

/-- 同じ小さい表示で元の全 native core を制限する Segal 射は自明 Kan。 -/
lemma cocartesianScaffoldStandardBridgeSourceSegalMap_id_trivialKanFibration :
    TrivialKanFibration (cocartesianScaffoldStandardBridgeSourceSegalMap n (𝟭 _) p q) := by
  have hR : TrivialKanFibration (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
      (Over.mk (cocartesianScaffoldSmallBridge n (𝟭 (ULift.{u} (Fin (n + 2))))))) := by
    rw [cocartesianScaffoldSmallBridge_id]
    exact cocartesianPullbackNativeLiftRestriction_scaffoldBridge_trivialKanFibration
      n p.val.hom q.val.hom
  exact ⟨trivialKanFibrations.comp_mem _ _ hR.mem (trivialKanFibrations.of_isIso _)⟩

/-- 全次元で元の全 Hom の同じ二成分への制限自身が自明 Kan。 -/
lemma cocartesianScaffoldSourceRestrictionMap_id_trivialKanFibration :
    TrivialKanFibration (cocartesianScaffoldSourceRestrictionMap n (𝟭 _) p q) := by
  have : IsIso (cocartesianScaffoldStandardSourcePullbackMap n (𝟭 _) p q) :=
    cocartesianScaffoldStandardSourcePullbackMap_isIso n _ p q
  have hf : cocartesianScaffoldSourceRestrictionMap n (𝟭 _) p q =
      cocartesianScaffoldStandardBridgeSourceSegalMap n (𝟭 _) p q ≫
        inv (cocartesianScaffoldStandardSourcePullbackMap n (𝟭 _) p q) := by
    rw [← cocartesianScaffoldSourceRestrictionMap_standard_factor, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [hf]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (cocartesianScaffoldStandardBridgeSourceSegalMap_id_trivialKanFibration n p q).mem
    (trivialKanFibrations.of_isIso _)⟩

/-- 同じ元の source 制限は、追加仮定なしに全次元で quasicategory の同値。 -/
lemma cocartesianScaffoldSourceRestrictionMap_id_isQCatEquivalence :
    IsQCatEquivalence (cocartesianScaffoldSourceRestrictionMap n (𝟭 _) p q) := by
  have := cocartesianScaffoldSourceRestrictionMap_id_trivialKanFibration n p q
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
