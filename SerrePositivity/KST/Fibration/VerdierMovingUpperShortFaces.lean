module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperCanonical
public import SerrePositivity.KST.Fibration.VerdierMovingUpperShortEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFamilyVertices

/-!
概要：動く上側再構成族の二短辺を、元の指定短辺の全族と有限両端へ厳密に戻す。
方針：同じホーン回収を二面へ制限し、元の第二短辺の両端回収を評価する。
規約：独立なホーン充填を選ばず、同じ実 canonical 族を保持する。
使われ方：K-6 c4 の指定有限二胞体の二短辺照合。
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
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌)

/-- 概要：同じ上側族の第一短辺は元の固定 core 包含の全区間族。
方針：同じ全ホーン回収を元の第一ホーン面へ制限する。
規約：全時刻の厳密等式。使われ方：指定有限端点の第一短辺条件。 -/
theorem verdierMovingUpperFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ verdierMovingUpperFamily d ℓ =
      (Δ[1] ◁ verdierMovingUpperFirstFamily d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
          (fullSRealizationKanObject d.left)) := by
  have h := congrArg (fun F => (horn₂₁.ι₀₁ ▷ (Δ[1] : SSet.{u + 1})) ≫ F)
    (verdierMovingUpperFamily_horn d ℓ)
  rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] at h
  exact h.trans (verdierMovingUpperHorn_first d)

/-- 概要：同じ上側族の第二短辺は元の全 S• 比較の動く合成端全族。
方針：同じ全ホーン回収を元の第二ホーン面へ制限する。
規約：非退化一単体を保持。使われ方：指定有限端点の第二短辺条件。 -/
theorem verdierMovingUpperFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ verdierMovingUpperFamily d ℓ =
      (Δ[1] ◁ verdierMovingUpperLastFamily d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (fullSRealizationKanObject d.left)
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))) := by
  have h := congrArg (fun F => (horn₂₁.ι₁₂ ▷ (Δ[1] : SSet.{u + 1})) ≫ F)
    (verdierMovingUpperFamily_horn d ℓ)
  rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] at h
  exact h.trans (verdierMovingUpperHorn_last d)

/-- 概要：固定第一短辺族の全頂点は元の同じ実 core 包含。
方針：元の定値族の零次の厳密回収を使う。
規約：元の実包含を保持。使われ方：両有限端点に共通する第一短辺。 -/
theorem verdierMovingUpperFirstFamily_point (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    (verdierMovingUpperFirstFamily d).app (Opposite.op ⦋0⦌) k =
      ULift.up (SimplicialCategory.homEquiv' _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
      (fullSRealizationKanObject d.left)))
    (ULift.up (SimplicialCategory.homEquiv' _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))))) 0 = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _

/-- 概要：同じ上側族の全有限パラメータで第一短辺は元の実 core 包含の標準区間像。
方針：同じ全短辺をそのパラメータで評価し、元の固定包含頂点へ戻す。
規約：特に両端で同じ実射。使われ方：指定有限二胞体の第一短辺条件。 -/
theorem verdierMovingUpperFamily_atVertex_firstFace (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) k =
      lift (𝟙 (Δ[1] : SSet.{u + 1}))
        (SSet.const (ULift.up (SimplicialCategory.homEquiv' _ _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
          (fullSRealizationKanObject d.left)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingUpperFamily_first]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
  rw [← Category.assoc, lift_whiskerLeft, SSet.const_comp, verdierMovingUpperFirstFamily_point]

/-- 概要：同じ上側族の始端の第二短辺は元の上側実完全射の標準区間像。
方針：同じ全短辺回収を始端で評価し、元の実作用頂点へ戻す。
規約：同じ元の実射。使われ方：指定上側始端の厳密二短辺照合。 -/
theorem verdierMovingUpperFamily_first_lastFace :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      lift (𝟙 (Δ[1] : SSet.{u + 1}))
        (SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
            verdierOriginalFullSCompositeMap d 0)))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (fullSRealizationKanObject d.left)
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingUpperFamily_last]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
  rw [← Category.assoc, lift_whiskerLeft, SSet.const_comp, verdierMovingUpperLastFamily_first]

/-- 概要：同じ上側族の終端の第二短辺は元の実包含・商の合成完全射の標準区間像。
方針：同じ全短辺回収を終端で評価し、元の実作用頂点へ戻す。
規約：元の実合成端を保持。使われ方：指定上側終端の厳密二短辺照合。 -/
theorem verdierMovingUpperFamily_last_lastFace :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      lift (𝟙 (Δ[1] : SSet.{u + 1}))
        (SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
            verdierOriginalFullSCompositeMap d 1)))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (fullSRealizationKanObject d.left)
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingUpperFamily_last]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
  rw [← Category.assoc, lift_whiskerLeft, SSet.const_comp, verdierMovingUpperLastFamily_last]

end SerrePositivity.KST.Fibration
