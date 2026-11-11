module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledNativeTriangle
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoherentHomFamilyVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativeFamilyControl

/-!
概要：元の二短辺の全族と、各入力で指定した全長 Hom を厳密に持つ実二胞体族。
方針：有限制御二単体を零骨格で指定し、同じ全ホーンへ延長する。
規約：ここでは全族空間間の encode と厳密切断は主張しない。
使われ方：Ind-S (9) の制御二胞体の構成部分。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ二短辺の全族と、指定した全ての入力の全 native Hom を回収する二胞体族。 -/
lemma controlledTriangleFamily_exists_with_native_vertices
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
      (Δ[1] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y))
    (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
      (Δ[1] ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z))
    (m : K _⦋0⦌ → (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶ SimplicialCategory.sHom X Z))
    (hm : ∀ k : K _⦋0⦌,
      (m k).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath) =
        SimplicialCategory.homEquiv' X Z
          (((SimplicialCategory.homEquiv' X Y).symm (f.app (Opposite.op ⦋0⦌) k).down) ≫
           ((SimplicialCategory.homEquiv' Y Z).symm (g.app (Opposite.op ⦋0⦌) k).down))) :
    ∃ F : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F = a ∧
      ∀ k : K _⦋0⦌,
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).obj ⟨ULift.up 0⟩ = X ∧
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).obj ⟨ULift.up 2⟩ = Z ∧
        HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
          (m k) := by
  obtain ⟨F₀, hF₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerHornFamily_exists_extension 2 1 (by decide) (by decide) K a
  have hfirst : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ F₀ =
      (Δ[1] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) := by
    have hh := (horn₂₁.ι₀₁ ▷ K) ≫= hF₀
    simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using hh.trans hf
  have hlast : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F₀ =
      (Δ[1] ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z) := by
    have hh := (horn₂₁.ι₁₂ ▷ K) ≫= hF₀
    simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using hh.trans hg
  let ff (k : K _⦋0⦌) := (SimplicialCategory.homEquiv' X Y).symm
    (f.app (Opposite.op ⦋0⦌) k).down
  let gg (k : K _⦋0⦌) := (SimplicialCategory.homEquiv' Y Z).symm
    (g.app (Opposite.op ⦋0⦌) k).down
  let s (k : K _⦋0⦌) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledNativeTriangle (ff k) (gg k) (m k) (hm k)
  obtain ⟨F, hF, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerHornFamily_exists_with_vertex_fillers 2 1
    (by decide) (by decide) K F₀ (fun k => SSet.yonedaEquiv.symm (s k)) (by
      intro k
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangle_horn_eq_of_faces
      all_goals
        apply SSet.yonedaEquiv.injective
        rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
          Equiv.apply_symm_apply]
      · erw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, hlast,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coherentHomIntervalFamily_vertex, Equiv.apply_symm_apply]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledNativeTriangle_last _ _ _ _
      · erw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, hfirst,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coherentHomIntervalFamily_vertex, Equiv.apply_symm_apply]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledNativeTriangle_first _ _ _ _)
  refine ⟨F, hF.trans hF₀, ?_⟩
  intro k
  rw [hv, Equiv.apply_symm_apply]
  exact ⟨rfl, rfl, heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledNativeTriangle_native (ff k) (gg k) (m k) (hm k))⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
