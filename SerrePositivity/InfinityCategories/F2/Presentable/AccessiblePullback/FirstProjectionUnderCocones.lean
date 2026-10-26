module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.UnderInputFamilyProperties
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ProjectionUnderCoconeRecovery
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ExtendedInputVertexValues
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactFiberOverProjection

/-!
概要：一般 accessible 成分の compact comma 第一射影の指定始点の下に全余錐を構成する。
方針：第一成分の指定始点を全入力に追加して相対交互構成し、元の under comma に厳密に戻す。
規約：元の全図式と標的を保持し、全小余極限は要求しない。
使われ方：第一成分射影の right cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：compact comma 第一射影の指定始点の下の小さい全試験図式は余錐を持つ。
方針：指定第一成分を含む元の入力族に交互構成を適用し、全値の一致で under comma に戻す。
規約：元の全入力と指定始点を保持し、第二脚の同値持ち上げは要求しない。
使われ方：一般 accessible 引き戻しの第一成分 cofinal 性。 -/
lemma nonempty_firstProjection_under_cocone_of_accessible_family
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {B : SSet.{u + 1}} [Quasicategory B] (hB : IsKappaAccessible μ B)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (hC : ∀ c, IsKappaAccessible μ (C c))
    (hCκ : ∀ c, Ind.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : Ind.HasSmallKappaFilteredColimits κ B)
    (p : ∀ c, C c ⟶ B) (hp : F1B.EquivalenceLifting (p 0))
    (hpμ : ∀ c, IsKappaAccessibleFunctor μ (p c))
    (hpκ : ∀ c, IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback (p 0) (p 1))
    (z : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u}) ⟶
      compactSourceSlice μ (x ≫ pullback.fst (p 0) (p 1)))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      pullback (sliceUnderProjection z) (componentCompactOverFst μ (p 0) (p 1) x)) :
    Nonempty (JoinCocone r) := by
  letI := hp.innerFibration
  let π := pullback.fst (p 0) (p 1)
  let F := componentCompactOverFst μ (p 0) (p 1) x
  let P := sliceUnderProjection z
  let t := r ≫ pullback.fst P F
  let a := r ≫ pullback.snd P F
  let U := a ≫ componentCompactOverInclusion μ (p 0) (p 1) x
  have hU : ∀ v, ComponentCompactVertex μ (p 0) (p 1)
      ((U ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) v) := by
    intro v
    exact fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) v)
  have hF : F ≫ compactSourceSliceInclusion μ (x ≫ π) =
      componentCompactOverInclusion μ (p 0) (p 1) x ≫ sliceOverPostcomp x π :=
    componentCompactOverFst_inclusion μ (p 0) (p 1) x
  have hbase : a ≫ F = t ≫ P := by
    dsimp only [a, t]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hinput : t ≫ P ≫ compactSourceSliceInclusion μ (x ≫ π) =
      U ≫ sliceOverPostcomp x π := by
    calc
      _ = (a ≫ F) ≫ compactSourceSliceInclusion μ (x ≫ π) := by
        exact (Category.assoc t P _).symm.trans
          (congrArg (fun g ↦ g ≫ compactSourceSliceInclusion μ (x ≫ π)) hbase.symm)
      _ = _ := by rw [Category.assoc, hF]; rfl
  let L := firstUnderInputShapes (Δ[0] : SSet.{u}) K
  letI := firstUnderInputShapes_quasicategory (Δ[0] : SSet.{u}) K
  have hμ : Cardinal.aleph0 < μ :=
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  have hsmall := firstUnderInputShapes_isKappaSmall
    (isKappaSmall_of_finite hμ.le (Δ[0] : SSet.{u})) hK
  let q := firstUnderInputDiagrams μ p x U t
  let i := firstUnderInputInclusions (Δ[0] : SSet.{u}) K
  let zc := firstUnderInputCocones μ p x U t
  have hi := firstUnderInputDiagrams_fixed μ p x U t hinput
  have hzi := firstUnderInputDiagrams_cocone_fixed μ p x U t hinput
  obtain ⟨R⟩ := exists_compactExtendedInputPullbackVertex_family h hK hB C L hsmall hC hCκ
    hBκ p hp hpμ hpκ hpCompact (U ≫ sliceOverProjection x) (sliceDiagramCocone U)
    q (firstUnderInputDiagrams_compact μ p x U t hU) i hi zc hzi
  let c := inputVertexSliceCocone U R.vertex
  let d := inputVertexSliceCocone (extendedSourceSliceDiagram μ (x ≫ π) t) R.first
  have hc : ComponentCompactVertex μ (p 0) (p 1)
      ((sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex) := by
    change ComponentCompactVertex μ (p 0) (p 1)
      ((sliceOverProjection x).app (Opposite.op ⦋0⦌) (inputVertexSliceCocone U R.vertex).vertex)
    rw [inputVertexSliceCocone_vertex_projection]
    exact R.compact
  have hcd : c.val ≫ sliceOverPostcomp x π =
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInr (Δ[0] : SSet.{u}) K)) (𝟙 Δ[0]) ≫ d.val := by
    exact inputVertexSliceCocone_postcomp_restrict_val π (i 0) U
      (extendedSourceSliceDiagram μ (x ≫ π) t) R.vertex R.first
      (ExtendedInputPullbackVertexData.first_uncurry μ p _ _ q i hi zc hzi R)
  exact nonempty_projectionUnderCocone_of_extended_cocones μ (p 0) (p 1) x π F hF z r
    c hc hc.1 d hcd

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
