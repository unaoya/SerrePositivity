module

public import SerrePositivity.InfinityCategories.F1B.Diagrams.PointJoinPrism
public import SerrePositivity.InfinityCategories.Core.NerveCone

/-!
概要：通常の圏の始対象の nerve を、その頂点を固定して収縮する。
方針：始対象からの標準錐に、点と nerve の join への prism を合成する。
規約：元の圏の始対象性を直接使い、cofinality や straightening を追加しない。
使われ方：undercategory の恒等射での cocartesian strict transport の評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：通常の始対象の nerve はその頂点を全パラメータで固定する始点収縮を持つ。
方針：標準始対象錐の両端と自己評価を join の prism に沿って移す。
規約：圏と射の宇宙は同じ u。
使われ方：一般の cocartesian fibration の strict transport の fiber 比較。 -/
lemma exists_kanNerveInitialPrism {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    ∃ C : (Δ[1] : SSet.{u}) ⊗ nerve I ⟶ nerve I,
      prismEndpoint 0 (nerve I) ≫ C = SSet.const (nerveVertex c) ∧
      prismEndpoint 1 (nerve I) ≫ C = 𝟙 _ ∧
      ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const (nerveVertex c) : K ⟶ nerve I)) ≫ C =
        SSet.const (nerveVertex c) := by
  let F := nerveInitialCone hc
  let C := cofinalPointJoinPrism (nerve I) ≫ F
  refine ⟨C, ?_, ?_, ?_⟩
  · dsimp only [C, F, nerveInitialCone]
    rw [← Category.assoc, cofinalPointJoinPrism_zero, Category.assoc,
      sliceUnderUncurry_fixed, nervePoint, SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  · dsimp only [C, F]
    rw [← Category.assoc, cofinalPointJoinPrism_one, nerveInitialCone_inr]
  · intro K
    dsimp only [C, F]
    rw [← Category.assoc, cofinalPointJoinPrism_naturality, Category.assoc]
    have hfact : (SSet.const (nerveVertex c) : K ⟶ nerve I) =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ nervePoint c := by
      rw [nervePoint, SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    have hmap : joinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.const (nerveVertex c) : K ⟶ nerve I) =
        joinMap (𝟙 (Δ[0] : SSet.{u}))
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) ≫
        joinMap (𝟙 (Δ[0] : SSet.{u})) (nervePoint c) := by
      rw [hfact]
      simpa only [Category.id_comp] using joinMap_comp (𝟙 (Δ[0] : SSet.{u})) (𝟙 _)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) (nervePoint c)
    rw [hmap]
    simp only [Category.assoc, nerveInitialCone_at_point, SSet.comp_const]

end SerrePositivity.InfinityCategories
