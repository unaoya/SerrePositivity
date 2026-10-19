module

public import SerrePositivity.InfinityCategories.F1B.KanSectionIntervalComparisonMono

public import SerrePositivity.InfinityCategories.F1.JoinDiagramRightRelativeExtension
public import SerrePositivity.InfinityCategories.F1B.KanSectionLeftIntervalFatNaturality
public import SerrePositivity.InfinityCategories.F1B.KanSectionLeftIntervalHomotopySection
public import SerrePositivity.InfinityCategories.F1.EquivalenceRetraction

/-!
概要：左 coslice fiber 写像空間と両端固定の区間写像空間の同値。
方針：coslice fiber の部分族を固定した相対 join 延長で厳密な左逆を作り、既存の右逆と比較する。
規約：比較射は既存の prism から定義した射そのもの。
使われ方：Kerodon §4.6.5–4.6.6、左右の写像空間の比較と unstraightening の fiber の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection
open PinchedInterval

/-- 概要：左 coslice fiber 模型から区間模型への比較射には厳密な左逆がある。
方針：区間模型全体の fat join 図式を、coslice fiber 模型の部分族と両端を保って回収する。
規約：左逆との合成はホモトピーでなく射の等式。
使われ方：Kerodon §4.6.6、写像空間比較の同値の単位。 -/
lemma cosliceFiberToIntervalMappingSpace_exists_retraction {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    ∃ r : intervalMappingSpace x y ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y,
      cosliceFiberToIntervalMappingSpace x y ≫ r = 𝟙 _ := by
  let c := cosliceFiberToIntervalMappingSpace x y
  let F := leftIntervalFatDiagram (𝟙 (intervalMappingSpace x y))
  let G := cosliceFiberUncurry (𝟙 (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y))
  have hFG : fatJoinMap (𝟙 (Δ[0] : SSet.{u})) c ≫ F =
      fatJoinComparison Δ[0] (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) ≫ G
        := by
    dsimp [F, G, c]
    rw [leftIntervalFatDiagram_precomp, Category.comp_id]
    simpa only [Category.id_comp] using leftIntervalFatDiagram_comparison (𝟙 (vertexFiber
      (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y))
  obtain ⟨H, hH, hy, hx⟩ := exists_joinDiagram_right_relative_extension c F G hFG
  have hx' : joinInl Δ[0] (intervalMappingSpace x y) ≫ H = SSet.yonedaEquiv.symm x := by
    rw [hx]
    exact leftIntervalFatDiagram_inl _
  have hy' : joinInr Δ[0] (intervalMappingSpace x y) ≫ H = SSet.const y := by
    rw [hy]
    exact leftIntervalFatDiagram_inr _
  refine ⟨cosliceFiberCurry H hx' hy', ?_⟩
  apply cosliceFiberUncurry_injective
  rw [cosliceFiberUncurry_precomp, cosliceFiberUncurry_curry]
  exact hH

/-- 概要：左 coslice fiber 模型の区間比較は quasicategory の同値。
方針：厳密な左逆と既存のホモトピー右逆を可逆二胞体で比較する。
規約：X は quasicategory、両写像空間は Kan 複体。
使われ方：Kerodon §4.6.6、coherent nerve の左右の写像空間の比較。 -/
lemma cosliceFiberToIntervalMappingSpace_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    IsQCatEquivalence (cosliceFiberToIntervalMappingSpace x y) := by
  obtain ⟨r, hr⟩ := cosliceFiberToIntervalMappingSpace_exists_retraction x y
  obtain ⟨b, ⟨hb⟩⟩ := cosliceFiberToIntervalMappingSpace_postcomp_essentiallySurjective
    (𝟙 (intervalMappingSpace x y))
  exact isQCatEquivalence_of_retraction_of_rightInverseIso _ r b hr hb

end SerrePositivity.InfinityCategories.KanSection
