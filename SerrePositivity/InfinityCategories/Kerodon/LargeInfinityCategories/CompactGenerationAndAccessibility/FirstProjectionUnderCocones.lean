module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.UnderInputFamilyProperties
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ProjectionUnderCoconeRecovery
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedInputVertexValues
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactFiberOverProjection

/-!
概要：一般 accessible 成分の compact comma 第一射影の指定始点の下に全余錐を構成する。
方針：第一成分の指定始点を全入力に追加して相対交互構成し、元の under comma に厳密に戻す。
規約：元の全図式と標的を保持し、全小余極限は要求しない。
使われ方：第一成分射影の right cofinal 性。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：compact comma 第一射影の指定始点の下の小さい全試験図式は余錐を持つ。
方針：指定第一成分を含む元の入力族に交互構成を適用し、全値の一致で under comma に戻す。
規約：元の全入力と指定始点を保持し、第二脚の同値持ち上げは要求しない。
使われ方：一般 accessible 引き戻しの第一成分 cofinal 性。 -/
lemma nonempty_firstProjection_under_cocone_of_accessible_family
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {K : SSet.{u}} [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {B : SSet.{u + 1}} [Quasicategory B] (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (hC : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (C c))
    (hCκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ B)
    (p : ∀ c, C c ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (p 0))
    (hpμ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (p c))
    (hpκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback (p 0) (p 1))
    (z : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.fst (p 0) (p 1)))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.componentCompactOverFst μ (p 0) (p 1) x)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) := by
  letI := hp.innerFibration
  let π := pullback.fst (p 0) (p 1)
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.componentCompactOverFst μ (p 0) (p 1) x
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z
  let t := r ≫ pullback.fst P F
  let a := r ≫ pullback.snd P F
  let U := a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentCompactOverInclusion μ (p 0) (p 1) x
  have hU : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ (p 0) (p 1)
      ((U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) v) := by
    intro v
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) v)
  have hF : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactSourceSliceInclusion μ (x ≫ π) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentCompactOverInclusion μ (p 0) (p 1) x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x π :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.componentCompactOverFst_inclusion μ (p 0) (p 1) x
  have hbase : a ≫ F = t ≫ P := by
    dsimp only [a, t]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hinput : t ≫ P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactSourceSliceInclusion μ (x ≫ π) =
      U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x π := by
    calc
      _ = (a ≫ F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactSourceSliceInclusion μ (x ≫ π) := by
        exact (Category.assoc t P _).symm.trans
          (congrArg (fun g ↦ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactSourceSliceInclusion μ (x ≫ π)) hbase.symm)
      _ = _ := by rw [Category.assoc, hF]; rfl
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputShapes (Δ[0] : SSet.{u}) K
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputShapes_quasicategory (Δ[0] : SSet.{u}) K
  have hμ : Cardinal.aleph0 < μ :=
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  have hsmall := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputShapes_isKappaSmall
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hμ.le (Δ[0] : SSet.{u})) hK
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputDiagrams μ p x U t
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputInclusions (Δ[0] : SSet.{u}) K
  let zc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputCocones μ p x U t
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputDiagrams_fixed μ p x U t hinput
  have hzi := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputDiagrams_cocone_fixed μ p x U t hinput
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compactExtendedInputPullbackVertex_family h hK hB C L hsmall hC hCκ
    hBκ p hp hpμ hpκ hpCompact (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone U)
    q (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputDiagrams_compact μ p x U t hU) i hi zc hzi
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.inputVertexSliceCocone U R.vertex
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.inputVertexSliceCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceDiagram μ (x ≫ π) t) R.first
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ (p 0) (p 1)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ (p 0) (p 1)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.inputVertexSliceCocone U R.vertex).vertex)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.inputVertexSliceCocone_vertex_projection]
    exact R.compact
  have hcd : c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x π =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K)) (𝟙 Δ[0]) ≫ d.val := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.inputVertexSliceCocone_postcomp_restrict_val π (i 0) U
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceDiagram μ (x ≫ π) t) R.vertex R.first
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedInputPullbackVertexData.first_uncurry μ p _ _ q i hi zc hzi R)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.nonempty_projectionUnderCocone_of_extended_cocones μ (p 0) (p 1) x π F hF z r
    c hc hc.1 d hcd

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
