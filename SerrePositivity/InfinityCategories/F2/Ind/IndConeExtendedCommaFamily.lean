module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedPrismOld
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramRightPrismRecovery

/-!
概要：全拡張データの元の C 全族と全円柱を、元の小さい図式形状の表示へ戻す。
方針：元の余錐形状の宇宙比較で前合成し、元の引き戻しと slice の射影を使う。
規約：新しい同型や持ち上げを選ばず、同じ全射を保持する。
使われ方：同じ元の diagram comma に余錐族を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeExtendedSliceData κ D q G)
/-- 概要：同じ元の図式 comma 内での補間後の全族。
方針：元の C 全族と全円柱を curry で戻す。規約：全射を保持。使われ方：実余錐。 -/
def indConeExtendedCommaFamily : join T (Δ[0] : SSet.{u + 1}) ⟶ diagramComma κ D :=
  diagramRightPrismFamily κ D (indConeExtendedFamily V) (indConeExtendedPrism V)
    (indConeExtendedPrism_source V) (indConeExtendedPrism_tip V)
/-- 概要：元の C の補間後の全図式を厳密に回収する。
方針：同じ実 comma の第一射影。規約：全係数を保持。使われ方：全境界の回収。 -/
lemma indConeExtendedCommaFamily_originalFamily :
    diagramCommaOriginalFamily κ D (indConeExtendedCommaFamily V) =
      indConeExtendedFamily V :=
  diagramRightPrismFamily_originalFamily _ _ _ _ _ _
/-- 概要：元の指定 D への補間後の全円柱を厳密に回収する。
方針：同じ実 comma の全余錐。規約：全射を保持。使われ方：全境界の回収。 -/
lemma indConeExtendedCommaFamily_prism :
    diagramCommaRightPrism κ D (indConeExtendedCommaFamily V) = indConeExtendedPrism V :=
  diagramRightPrismFamily_prism _ _ _ _ _ _
/-- 概要：補間後の全族は旧族の元の q を厳密に回収する。
方針：元の C 全図式と全円柱を同時に照合。規約：同型でなく等号。使われ方：実余錐。 -/
lemma indConeExtendedCommaFamily_old :
    joinInl T (Δ[0] : SSet.{u + 1}) ≫ indConeExtendedCommaFamily V = q := by
  apply diagramComma_rightFamily_ext κ D
  · rw [← diagramCommaOriginalFamily_precomp, indConeExtendedCommaFamily_originalFamily,
      indConeExtendedFamily_old]
  · rw [← diagramCommaRightPrism_precomp, indConeExtendedCommaFamily_prism,
      indConeExtendedPrism_old]
/-- 概要：同じ元の図式 comma での、元の q 自身の実余錐。
方針：元の全境界の等号を使う。規約：元の q を保持。使われ方：点追加の filtered 性。 -/
def indConeExtendedCommaCocone : JoinCocone q :=
  ⟨indConeExtendedCommaFamily V, indConeExtendedCommaFamily_old V⟩
end SerrePositivity.InfinityCategories.F2.Ind
