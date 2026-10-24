module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedPrismLower
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedCommaFamily

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
/-- 概要：元の全図式 comma で補間族の下方制限は指定 G 自身の全族。
方針：元の C 全図式と全円柱の両方で照合。規約：全射の等号。使われ方：指定余錐の保持。 -/
lemma indConeExtendedCommaFamily_lower :
    indConeExtendedCommaFamily V ≫
      diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})) = G.val := by
  apply diagramComma_rightFamily_ext κ
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D)
  · rw [← diagramCommaOriginalFamily_restrict, indConeExtendedCommaFamily_originalFamily,
      indConeExtendedFamily_lower]
  · rw [← diagramCommaRightPrism_restrict, indConeExtendedCommaFamily_prism,
      indConeExtendedPrism_lower]
/-- 概要：元の実余錐の下方制限は、指定された余錐 G 自身。
方針：全余錐の実写像の等号。規約：同型への置換なし。使われ方：有限半順序図式の貼合せ。 -/
lemma indConeExtendedCommaCocone_lower :
    mapJoinCocone (diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))
      (indConeExtendedCommaCocone V) = G := by
  apply Subtype.ext
  exact indConeExtendedCommaFamily_lower V
/-- 概要：元の小さい全試験族は指定下方余錐 G を厳密に固定して延長できる。
方針：実全拡張と指定下方境界の回収。規約：追加の充填入力なし。使われ方：点追加の貼合せ。 -/
lemma exists_indConeDiagramComma_cocone_fixing_lower [Fact κ.IsRegular] {A : SSet.{u}}
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u}))))
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L) :
    ∃ c : JoinCocone q,
      mapJoinCocone (diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u}))) c = G := by
  obtain ⟨V⟩ := indConeExtendedSliceData_nonempty κ D q G hA hL
  exact ⟨indConeExtendedCommaCocone V, indConeExtendedCommaCocone_lower V⟩
end SerrePositivity.InfinityCategories.F2.Ind
