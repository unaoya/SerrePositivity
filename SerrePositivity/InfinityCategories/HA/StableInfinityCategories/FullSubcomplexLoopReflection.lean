module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.FullSubcomplexInitialReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexFunctorFaithful
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.FullSubcomplexLimitReflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SquareConePostcomp
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SquareFamilyReading

/-!
概要：全部分複体への同じ零頂点・引き戻し四角形・loop 図式の反映をまとめる。
方針：零頂点は始終対象の反映、引き戻しは元の極限錐の反映、loop はその三条件を使う。
使われ方：HA §1.1.3、Kerodon §7.1（Tag 02H1）の全部分圏の指定極限の反映。
規約：周囲の元の四角形のまま判定し、新しい四角形は選ばない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open ZeroObjects

/-- 元の全部分複体の頂点が周囲で零なら、内部でも同じ零頂点。 -/
lemma fullSubcomplexOnVertices_isZeroVertex_of_image {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (x : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (hx : IsZeroVertex x.val) : IsZeroVertex x :=
  ⟨fullSubcomplexOnVertices_isInitialVertex_of_image P x hx.1,
    (isFullyFaithful_fullSubcomplexOnVertices_ι X P).reflects_isTerminalVertex hx.2⟩

/-- 元の全部分複体の四角形が周囲で引き戻しなら、内部でも引き戻し。 -/
lemma fullSubcomplexOnVertices_isPullbackSquare_of_image {X : SSet.{u}}
    (P : X _⦋0⦌ → Prop)
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (hR : IsPullbackSquare (R ≫ (fullSubcomplexOnVertices X P).ι)) : IsPullbackSquare R :=
  isLimitCone_of_fullSubcomplex P (pullbackCone R)
    ((isLimitCone_map_pullbackCone_iff (fullSubcomplexOnVertices X P).ι R).mpr hR)

/-- 元の全部分複体の同じ四角形の頂点は、周囲で loop 図式なら内部でも loop 図式。 -/
lemma isLoopDiagramVertex_of_fullSubcomplex {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop)
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj
      (fullSubcomplexOnVertices X P : SSet.{u})) _⦋0⦌)
    (hv : IsLoopDiagramVertex
      (((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map (fullSubcomplexOnVertices X P).ι).app _ v)) :
    IsLoopDiagramVertex v := by
  have hd : squareDiagram
      (((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map (fullSubcomplexOnVertices X P).ι).app _ v) =
      squareDiagram v ≫ (fullSubcomplexOnVertices X P).ι :=
    functorVertexSquare_postcompose v _
  dsimp only [IsLoopDiagramVertex] at hv ⊢
  rw [hd] at hv
  exact ⟨fullSubcomplexOnVertices_isZeroVertex_of_image P _ hv.1,
    fullSubcomplexOnVertices_isZeroVertex_of_image P _ hv.2.1,
    fullSubcomplexOnVertices_isPullbackSquare_of_image P _ hv.2.2⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
