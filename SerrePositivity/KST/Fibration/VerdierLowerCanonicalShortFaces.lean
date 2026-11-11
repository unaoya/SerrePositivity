module
public import SerrePositivity.KST.Fibration.VerdierLowerCanonicalReadout
public import SerrePositivity.KST.Fibration.VerdierMovingUpperFirstComparison

/-!
概要：正規化下側と元の実下側の二短辺・全 native Hom を同じ時刻で照合する。
方針：同じホーン回収を二短辺へ制限し、両端座標を回収して native 読出しを反映する。
規約：二胞体の外延性は F1 正本に残し、元の族との厳密等号を先取りしない。
使われ方：K-6 c4 の正規化四角柱の下側有限端点の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
private theorem lowerNativeCoordinateReflection
    (A B : (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hf : stdSimplex.δ (2 : Fin 3) ≫ A = stdSimplex.δ (2 : Fin 3) ≫ B)
    (hg : stdSimplex.δ (0 : Fin 3) ≫ A = stdSimplex.δ (0 : Fin 3) ≫ B)
    (hn : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv A).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv B).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) :
    HEq ((SSet.yonedaEquiv A).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      ((SSet.yonedaEquiv B).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  have hs := congrArg (fun f : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
    (SSet.yonedaEquiv f).obj ⟨ULift.up 0⟩) hf
  have ht := congrArg (fun f : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
    (SSet.yonedaEquiv f).obj ⟨ULift.up 1⟩) hg
  have hs' : (SSet.yonedaEquiv A).obj ⟨ULift.up 0⟩ =
      (SSet.yonedaEquiv B).obj ⟨ULift.up 0⟩ := by
    simpa [stdSimplex.yonedaEquiv_δ_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity, SimplicialObject.δ,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplex_map_obj, SimplexCategory.δ] using hs
  have ht' : (SSet.yonedaEquiv A).obj ⟨ULift.up 2⟩ =
      (SSet.yonedaEquiv B).obj ⟨ULift.up 2⟩ := by
    simpa [stdSimplex.yonedaEquiv_δ_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity, SimplicialObject.δ,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplex_map_obj, SimplexCategory.δ] using ht
  exact verdierNativeReadout_vertex_heq hs' ht' _ _ hn

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierLowerCanonicalLongSpace d) _⦋0⦌)

/-- 概要：正規化下側の第一短辺は元の下側の全第一短辺。
方針：同じ実ホーンの第一包含へ制限する。
規約：全族の厳密等式。使われ方：有限端点の第一面照合。 -/
theorem verdierLowerCanonicalFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierLowerCanonicalFamily d ℓ =
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (verdierFullSLowerDeformation d).h := by
  have hn := congrArg (fun f => (horn₂₁.ι₀₁ ▷ (Δ[1] : SSet.{u + 1})) ≫ f)
    (verdierLowerCanonicalFamily_horn d ℓ)
  have hr := congrArg (fun f => (horn₂₁.ι₀₁ ▷ (Δ[1] : SSet.{u + 1})) ≫ f)
    (verdierFullSLowerDeformation_horn d)
  simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using hn.trans hr.symm

/-- 概要：正規化下側の第二短辺は元の下側の全第二短辺。
方針：同じ実ホーンの第二包含へ制限する。
規約：全族の厳密等式。使われ方：有限端点の第二面照合。 -/
theorem verdierLowerCanonicalFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierLowerCanonicalFamily d ℓ =
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (verdierFullSLowerDeformation d).h := by
  have hn := congrArg (fun f => (horn₂₁.ι₁₂ ▷ (Δ[1] : SSet.{u + 1})) ≫ f)
    (verdierLowerCanonicalFamily_horn d ℓ)
  have hr := congrArg (fun f => (horn₂₁.ι₁₂ ▷ (Δ[1] : SSet.{u + 1})) ≫ f)
    (verdierFullSLowerDeformation_horn d)
  simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using hn.trans hr.symm

/-- 概要：各時刻の第一短辺は元の下側の同じ時刻の面。
方針：全短辺の等式を指定頂点で評価する。
規約：元の時刻を保持。使われ方：有限二胞体の第一面条件。 -/
theorem verdierLowerCanonicalFamily_vertex_first (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) k =
      stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp,
    verdierLowerCanonicalFamily_first]

/-- 概要：各時刻の第二短辺は元の下側の同じ時刻の面。
方針：全短辺の等式を指定頂点で評価する。
規約：元の時刻を保持。使われ方：有限二胞体の第二面条件。 -/
theorem verdierLowerCanonicalFamily_vertex_last (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) k =
      stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp,
    verdierLowerCanonicalFamily_last]

/-- 概要：同じ実読出しの正規化下側と元の下側の全 native 長 Hom は各時刻で一致。
方針：二短辺から両端を回収し、同じ全関手頂点の native 回収を反映する。
規約：二胞体そのものの外延性は使わない。
使われ方：下側有限端点の第三照合条件。 -/
theorem verdierLowerCanonicalReadout_vertex_native
    (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
    (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])
    (hL : VerdierLowerNativeReadoutRecovery d L)
    (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
      (verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull)) k)).map
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k)).map
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  exact lowerNativeCoordinateReflection _ _
    (verdierLowerCanonicalFamily_vertex_first d (verdierLowerCanonicalReadout d L hfull) k)
    (verdierLowerCanonicalFamily_vertex_last d (verdierLowerCanonicalReadout d L hfull) k)
    (verdierLowerCanonicalReadout_native d L hfull hL k)

end SerrePositivity.KST.Fibration
