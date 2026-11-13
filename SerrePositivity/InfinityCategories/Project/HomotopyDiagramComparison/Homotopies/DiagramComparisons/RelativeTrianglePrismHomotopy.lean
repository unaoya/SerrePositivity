module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.RelativeExtensionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.F1DiagramsTrianglePrism

/-!
概要：同じ底と二辺を持つ三角形 prism を、その両方を保つ一つの円柱で比較する。
方針：二辺の押し出しで内ホーンへの制限を照合し、相対延長空間の自明 Kan 性を使う。
規約：長辺だけの同型へ落とさず、三角形全体と二辺の固定条件を保持する。
使われ方：native な二単体を用いた輸送比較の高次整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 三角形の最初と最後の辺で一致する prism は、同じ内ホーン上で一致する。 -/
lemma trianglePrism_hornRestriction_eq {A E : SSet.{u}}
    (T T' : (Δ[2] : SSet.{u}) ⊗ A ⟶ E)
    (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T =
      (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T')
    (hsecond : (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T =
      (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T') :
    ((horn 2 1).ι ▷ A) ≫ T = ((horn 2 1).ι ▷ A) ≫ T' := by
  apply (horn₂₁.isPushout.map (tensorRight A)).hom_ext
  · change (horn₂₁.ι₀₁ ▷ A) ≫ ((horn 2 1).ι ▷ A) ≫ T =
      (horn₂₁.ι₀₁ ▷ A) ≫ ((horn 2 1).ι ▷ A) ≫ T'
    simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using hfirst
  · change (horn₂₁.ι₁₂ ▷ A) ≫ ((horn 2 1).ι ▷ A) ≫ T =
      (horn₂₁.ι₁₂ ▷ A) ≫ ((horn 2 1).ι ▷ A) ≫ T'
    simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using hsecond

/-- 二辺と底を共有する三角形 prism は、二辺と底を厳密に保つ円柱で比較できる。 -/
lemma exists_trianglePrism_homotopy_relative_spine {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (β : (Δ[2] : SSet.{u}) ⊗ A ⟶ B)
    (T T' : (Δ[2] : SSet.{u}) ⊗ A ⟶ E) (hT : T ≫ p = β) (hT' : T' ≫ p = β)
    (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T =
      (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T')
    (hsecond : (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T =
      (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T') :
    ∃ H : SSet.Homotopy T T',
      H.h ≫ p = fst ((Δ[2] : SSet.{u}) ⊗ A) Δ[1] ≫ β ∧
      ((stdSimplex.δ (2 : Fin 3) ▷ A) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst ((Δ[1] : SSet.{u}) ⊗ A) Δ[1] ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T' ∧
      ((stdSimplex.δ (0 : Fin 3) ▷ A) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst ((Δ[1] : SSet.{u}) ⊗ A) Δ[1] ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T' := by
  let i := (horn 2 1).ι ▷ A
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_horn_whiskerRight (1 : Fin 2) A
  have hs := trianglePrism_hornRestriction_eq T T' hfirst hsecond
  obtain ⟨H, hbase, hspine⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_homotopy_over_fixed_extension p β i hi (i ≫ T')
    (by rw [Category.assoc, hT']) T T' hT hT' hs rfl
  refine ⟨H, hbase, ?_, ?_⟩
  · have h := congrArg (fun z ↦ ((horn₂₁.ι₀₁ ▷ A) ▷ (Δ[1] : SSet.{u})) ≫ z) hspine
    dsimp only [i] at h
    rw [← Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight, horn.ι_ι] at h
    simp only [← Category.assoc, whiskerRight_fst] at h
    rw [Category.assoc (fst _ _) (horn₂₁.ι₀₁ ▷ A) ((horn 2 1).ι ▷ A),
      ← comp_whiskerRight, horn.ι_ι] at h
    simpa only [Category.assoc] using h
  · have h := congrArg (fun z ↦ ((horn₂₁.ι₁₂ ▷ A) ▷ (Δ[1] : SSet.{u})) ≫ z) hspine
    dsimp only [i] at h
    rw [← Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight, horn.ι_ι] at h
    simp only [← Category.assoc, whiskerRight_fst] at h
    rw [Category.assoc (fst _ _) (horn₂₁.ι₁₂ ▷ A) ((horn 2 1).ι ▷ A),
      ← comp_whiskerRight, horn.ι_ι] at h
    simpa only [Category.assoc] using h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
