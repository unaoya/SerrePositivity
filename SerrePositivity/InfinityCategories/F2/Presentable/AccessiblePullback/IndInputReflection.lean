module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.IndBaseResolution

/-!
概要：Ind 模型での固定入力上の比較同型を元の底へ反映する。
方針：共通解像の自明 Kan 射で同型を回収し、元の底への射影と厳密な切断を相殺する。
規約：入力と標的の全図式を保つ。
使われ方：元の引き戻し内の compact 成分対の厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：Ind 模型へ送った入力付き頂点の同型は元の底の同じ入力上の同型へ戻る。
方針：Ind 射影の二重 slice 後合成の充満忠実性で同型を取り、元の底への射影で戻す。
規約：元の二つの頂点と全入力を厳密に回収する。
使われ方：相対交互構成で得た最終比較同型の元の底への降下。 -/
lemma IndBaseResolution.nonempty_inputVertexIso_of_comparison
    {μ : Cardinal.{u}} {B K : SSet.{u + 1}} [Quasicategory B]
    (R : IndBaseResolution μ B) (q : K ⟶ B) (z : JoinCocone q)
    {u v : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder q)).symm z)) _⦋0⦌}
    (e : Nonempty (VertexIso
      ((stableInputPostcomp q R.comparison (q ≫ R.comparison) rfl z
        (mapJoinCocone R.comparison z) rfl).app (Opposite.op ⦋0⦌) u)
      ((stableInputPostcomp q R.comparison (q ≫ R.comparison) rfl z
        (mapJoinCocone R.comparison z) rfl).app (Opposite.op ⦋0⦌) v))) :
    Nonempty (VertexIso u v) := by
  let qt := q ≫ R.toResolution
  let zt := mapJoinCocone R.toResolution z
  let qm := q ≫ R.comparison
  let zm := mapJoinCocone R.comparison z
  let T := stableInputPostcomp q R.toResolution qt rfl z zt rfl
  let S := stableInputPostcomp qt R.toModel qm (Category.assoc q R.toResolution R.toModel)
    zt zm (Category.assoc z.val R.toResolution R.toModel)
  have hq : qt ≫ R.toBase = q := by
    dsimp only [qt]
    rw [Category.assoc, R.section_property, Category.comp_id]
  have hz : zt.val ≫ R.toBase = z.val := by
    change (z.val ≫ R.toResolution) ≫ R.toBase = z.val
    rw [Category.assoc, R.section_property, Category.comp_id]
  let U := stableInputPostcomp qt R.toBase q hq zt z hz
  have hTS : T ≫ S = stableInputPostcomp q R.comparison qm rfl z zm rfl := by
    exact stableInputPostcomp_comp q R.toResolution qt rfl R.toModel qm
      (Category.assoc q R.toResolution R.toModel) z zt zm rfl
      (Category.assoc z.val R.toResolution R.toModel)
  have hTU : T ≫ U = 𝟙 _ := by
    have h := stableInputPostcomp_comp q R.toResolution qt rfl R.toBase q hq z zt z rfl hz
    simpa only [R.section_property, stableInputPostcomp_id] using h
  have hS : TrivialKanFibration S :=
    stableInputPostcomp_trivialKanFibration qt R.toModel qm
      (Category.assoc q R.toResolution R.toModel) zt zm
      (Category.assoc z.val R.toResolution R.toModel)
  have hu (x : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder q)).symm z)) _⦋0⦌) :
      U.app (Opposite.op ⦋0⦌) (T.app (Opposite.op ⦋0⦌) x) = x := by
    exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) hTU
  obtain ⟨e⟩ := e
  have e' : VertexIso ((T ≫ S).app (Opposite.op ⦋0⦌) u)
      ((T ≫ S).app (Opposite.op ⦋0⦌) v) := by
    rw [hTS]
    exact e
  let e₀ := (isQCatEquivalence_of_trivialKanFibration S).isFullyFaithful.preimageVertexIso e'
  have e₁ := VertexIso.map e₀ U
  change VertexIso (U.app (Opposite.op ⦋0⦌) (T.app (Opposite.op ⦋0⦌) u))
    (U.app (Opposite.op ⦋0⦌) (T.app (Opposite.op ⦋0⦌) v)) at e₁
  exact ⟨by simpa only [hu] using e₁⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
