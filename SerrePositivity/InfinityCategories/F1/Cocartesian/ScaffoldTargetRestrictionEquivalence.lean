module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldStandardTargetFactorization

/-!
概要：元の分類先の最初の辺と尾部への同じ制限は全次元で自明 Kan。
方針：同じ大きい Segal 制限の自明 Kan 性を表示同型で移す。
規約：元の分類図式と全パラメーターの制限を保持する。
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

/-- 全次元で元の分類先の同じ二成分への制限自身は自明 Kan。 -/
lemma cocartesianScaffoldTargetRestrictionMap_id_trivialKanFibration :
    TrivialKanFibration (cocartesianScaffoldTargetRestrictionMap n (𝟭 _) p q) := by
  have : IsIso (cocartesianScaffoldStandardTargetPullbackMap n (𝟭 _) p q) :=
    cocartesianScaffoldStandardTargetPullbackMap_isIso n _ p q
  have hf : cocartesianScaffoldTargetRestrictionMap n (𝟭 _) p q =
      cocartesianScaffoldTargetSegalMap n (𝟭 _) p q ≫
        inv (cocartesianScaffoldStandardTargetPullbackMap n (𝟭 _) p q) := by
    rw [← cocartesianScaffoldTargetRestrictionMap_standard_factor, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [hf]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (cocartesianScaffoldTargetSegalMap_id_trivialKanFibration n p q).mem
    (trivialKanFibrations.of_isIso _)⟩

/-- 同じ元の target 制限は、追加仮定なしに全次元で quasicategory の同値。 -/
lemma cocartesianScaffoldTargetRestrictionMap_id_isQCatEquivalence :
    IsQCatEquivalence (cocartesianScaffoldTargetRestrictionMap n (𝟭 _) p q) := by
  have := cocartesianScaffoldTargetRestrictionMap_id_trivialKanFibration n p q
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
