module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTriangleComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightAnodyneJoinPrefix

/-!
概要：二つの指定辺を、その両方と指定した底の二単体を保つ実際の三角形へ延長する。
方針：指定した二辺を内ホーンの押し出しで貼り、inner fibration の持ち上げを取る。
規約：底の辺の型付き表示を変えず、二辺の全単体表示を厳密に保つ。
使われ方：標準の左輸送辺に実際の付加比較辺を前置する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 二つの点の join に、前の点を加える終端辺の包含。 -/
lemma joinEdgePoint_terminalFace :
    joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) ≫
        (joinStdSimplexIso 1 0).hom =
      (joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ (0 : Fin 3) := by
  apply DGNerve.join_hom_to_stdSimplex_ext
  · simp only [← Category.assoc, joinInl_joinMap]
    simp only [Category.assoc, DGNerve.joinStdSimplexIso_inl]
    apply SSet.yonedaEquiv.injective
    decide
  · simp only [← Category.assoc, joinInr_joinMap, Category.id_comp]
    simp only [DGNerve.joinStdSimplexIso_inr]
    apply SSet.yonedaEquiv.injective
    decide

/-- 三角形の終端辺の包含は right anodyne。 -/
lemma triangleTerminalFace_rightAnodyne :
    rightAnodyneExtensions (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) := by
  have h := joinMap_rightAnodyne (stdSimplex.δ (0 : Fin 2))
    (Δ[0] : SSet.{u}) endpointInclusion_rightAnodyne
  have h' := rightAnodyneExtensions.comp_mem _ (joinStdSimplexIso 1 0).hom h
    (MorphismProperty.llp_of_isIso _ _)
  rw [joinEdgePoint_terminalFace] at h'
  exact (rightAnodyneExtensions.cancel_left_of_respectsIso (joinStdSimplexIso 0 0).hom _).mp h'

/-- 指定した二辺と底の二単体を保つ、実際の三角形の持ち上げが存在する。 -/
lemma exists_prefixTriangle_over_innerFibration {E B : SSet.{u}}
    (q : E ⟶ B) [InnerFibration q]
    (a b : (Δ[1] : SSet.{u}) ⟶ E)
    (ha : stdSimplex.δ (0 : Fin 2) ≫ a = stdSimplex.δ (1 : Fin 2) ≫ b)
    (v : (Δ[2] : SSet.{u}) ⟶ B)
    (he : stdSimplex.δ (2 : Fin 3) ≫ v = a ≫ q)
    (ht : stdSimplex.δ (0 : Fin 3) ≫ v = b ≫ q) :
    ∃ s : (Δ[2] : SSet.{u}) ⟶ E,
      stdSimplex.δ (2 : Fin 3) ≫ s = a ∧
      stdSimplex.δ (0 : Fin 3) ≫ s = b ∧ s ≫ q = v := by
  let W := horn₂₁.isPushout.desc a b ha
  have hfirst : horn₂₁.ι₀₁ ≫ W = a := horn₂₁.isPushout.inl_desc _ _ _
  have hsecond : horn₂₁.ι₁₂ ≫ W = b := horn₂₁.isPushout.inr_desc _ _ _
  have hw : W ≫ q = (horn 2 1).ι ≫ v := by
    apply horn₂₁.isPushout.hom_ext
    · simp only [← Category.assoc, hfirst, horn.ι_ι, he]
    · simp only [← Category.assoc, hsecond, horn.ι_ι, ht]
  have : HasLiftingProperty (horn 2 (1 : Fin 3)).ι q :=
    InnerFibration.mem _ (horn_ι_mem_innerHornInclusions (by decide) (by decide))
  let sq : CommSq W (horn 2 (1 : Fin 3)).ι q v := ⟨hw⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← horn.ι_ι_assoc (1 : Fin 3) 2 (by decide), sq.fac_left]
    exact hfirst
  · rw [← horn.ι_ι_assoc (1 : Fin 3) 0 (by decide), sq.fac_left]
    exact hsecond

end
end SerrePositivity.InfinityCategories.HomotopyLimits
