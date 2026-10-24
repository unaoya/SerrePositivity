module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanRelativePathLifting
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TrivialFibrationHomotopy

/-!
概要：Kan fibration の底の指定した可逆経路の全パラメータ族を、指定端点を保って持ち上げる。
方針：相対経路写像の自明 Kan fibration の切断を選び、入力した経路と端点の組を写す。
規約：底の経路全体を厳密に保つ。使われ方：指定した共通部分のホモトピーに沿う余錐の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}} [KanComplex E] [KanComplex B]
  (p : E ⟶ B) [HomotopicalAlgebra.Fibration p] (j : Fin 2)

/-- 指定端点の相対経路写像の切断を一つ選ぶ。 -/
def kanRelativePathSection : relativeEquivalencePathTargetAt p j ⟶ equivalencePath E := by
  have := relativeEquivalencePathMapAt_trivialKanFibration_of_fibration p j
  exact (trivialKanFibration_exists_section (relativeEquivalencePathMapAt p j)).choose

/-- 相対経路の切断は、底の経路と指定端点の組を厳密に保つ。 -/
lemma kanRelativePathSection_map :
    kanRelativePathSection p j ≫ relativeEquivalencePathMapAt p j = 𝟙 _ := by
  have := relativeEquivalencePathMapAt_trivialKanFibration_of_fibration p j
  exact (trivialKanFibration_exists_section (relativeEquivalencePathMapAt p j)).choose_spec

variable (a : T ⟶ E) (h : T ⟶ equivalencePath B)
  (ha : h ≫ equivalencePathEndpoint B j = a ≫ p)

/-- 入力した底の経路族を、入力した端点族から全体を保って持ち上げる。 -/
def kanSpecifiedPathLift : T ⟶ equivalencePath E :=
  pullback.lift h a ha ≫ kanRelativePathSection p j

/-- 持ち上げた経路族の底は、入力した経路族そのもの。 -/
lemma kanSpecifiedPathLift_projection :
    kanSpecifiedPathLift p j a h ha ≫ equivalencePathMap p = h := by
  rw [← relativeEquivalencePathMapAt_fst p j, kanSpecifiedPathLift,
    ← Category.assoc, Category.assoc _ (kanRelativePathSection p j),
    kanRelativePathSection_map, Category.comp_id, pullback.lift_fst]

/-- 持ち上げた経路族は、入力した指定端点の族を厳密に保つ。 -/
lemma kanSpecifiedPathLift_endpoint :
    kanSpecifiedPathLift p j a h ha ≫ equivalencePathEndpoint E j = a := by
  rw [← relativeEquivalencePathMapAt_snd p j, kanSpecifiedPathLift,
    ← Category.assoc, Category.assoc _ (kanRelativePathSection p j),
    kanRelativePathSection_map, Category.comp_id, pullback.lift_snd]

/-- 持ち上げの反対の端点も、底の指定経路の反対の端点へ厳密に写る。 -/
lemma kanSpecifiedPathLift_other_endpoint :
    (kanSpecifiedPathLift p j a h ha ≫ equivalencePathEndpoint E j.rev) ≫ p =
      h ≫ equivalencePathEndpoint B j.rev := by
  rw [Category.assoc, ← equivalencePathMap_endpoint p j.rev, ← Category.assoc,
    kanSpecifiedPathLift_projection]

/-- パラメータの変更は、同じ切断で作る指定経路の持ち上げと厳密に可換。 -/
lemma kanSpecifiedPathLift_precomp {S : SSet.{u}} (i : S ⟶ T) :
    kanSpecifiedPathLift p j (i ≫ a) (i ≫ h)
        (by rw [Category.assoc, ha, Category.assoc]) =
      i ≫ kanSpecifiedPathLift p j a h ha := by
  simp only [kanSpecifiedPathLift, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd,
    Category.assoc]

/-- 同じ経路と指定端点を持つ二つの持ち上げは、その経路と端点を保つホモトピーで結べる。 -/
lemma kanSpecifiedPathLift_unique_homotopy (l : T ⟶ equivalencePath E)
    (hl : l ≫ equivalencePathMap p = h) (hlj : l ≫ equivalencePathEndpoint E j = a) :
    ∃ H : SSet.Homotopy (kanSpecifiedPathLift p j a h ha) l,
      H.h ≫ equivalencePathMap p = fst T (Δ[1] : SSet.{u}) ≫ h ∧
      H.h ≫ equivalencePathEndpoint E j = fst T (Δ[1] : SSet.{u}) ≫ a := by
  have := relativeEquivalencePathMapAt_trivialKanFibration_of_fibration p j
  have hh : kanSpecifiedPathLift p j a h ha ≫ relativeEquivalencePathMapAt p j =
      l ≫ relativeEquivalencePathMapAt p j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeEquivalencePathMapAt_fst,
        kanSpecifiedPathLift_projection, hl]
    · simp only [Category.assoc, relativeEquivalencePathMapAt_snd,
        kanSpecifiedPathLift_endpoint, hlj]
  obtain ⟨H, hH⟩ := exists_homotopy_over_trivialKanFibration
    (relativeEquivalencePathMapAt p j) (kanSpecifiedPathLift p j a h ha) l hh
  refine ⟨H, ?_, ?_⟩
  · have h₁ := congrArg (fun t ↦ t ≫ pullback.fst (equivalencePathEndpoint B j) p) hH
    simpa only [Category.assoc, relativeEquivalencePathMapAt_fst, hl] using h₁
  · have h₁ := congrArg (fun t ↦ t ≫ pullback.snd (equivalencePathEndpoint B j) p) hH
    simpa only [Category.assoc, relativeEquivalencePathMapAt_snd, hlj] using h₁

end
end SerrePositivity.InfinityCategories.HomotopyLimits
