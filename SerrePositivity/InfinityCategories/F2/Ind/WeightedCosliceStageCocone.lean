module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTotalCoslice
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedStagePrismAssembly
public import SerrePositivity.InfinityCategories.F2.Ind.ColimitCosliceStageFactorization
public import SerrePositivity.InfinityCategories.F2.Ind.CoslicePullbackStageCocone
public import SerrePositivity.InfinityCategories.F2.Ind.PullbackFixedPrism
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeOfPrism

/-!
概要：元の全比較の coslice 図式の終点が一段に入れば、同じ coslice 内に余錐がある。
方針：元の全 join を後続段へ下ろし、値を固定した二段間の円柱と段内の余錐を合わせる。
規約：元の coslice 図式全体を保持。使われ方：全比較の coslice の κ-filtered 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]

/-- 同じ一段を終点に持つ元の coslice 図式は、元の引き戻し内に余錐を持つ。 -/
lemma nonempty_weightedTotalCoslice_cocone_of_stage
    (x : (colimit (rightFibrationTotalDiagram F)) _⦋0⦌) {K : SSet.{u}}
    (hK : IsKappaSmall κ K) (a : K ⟶ weightedTotalCoslice F x)
    (i : I) (g : K ⟶ (F.obj i).val.left)
    (ha : a ≫ pullback.fst _ _ = g ≫ weightedNerveConstantLift (rightFibrationTotalDiagram F) i) :
    Nonempty (JoinCocone a) := by
  have (j : I) : Quasicategory ((rightFibrationTotalDiagram F).obj j) :=
    quasicategory_of_innerFibration (F.obj j).val.hom
  have (j : I) : IsKappaFiltered κ ((rightFibrationTotalDiagram F).obj j) :=
    inferInstanceAs (IsKappaFiltered κ (F.obj j).val.left)
  let f := strictRightFibrationTotalAssembly F
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have : Quasicategory (pullback f p) := weightedTotalCoslice_quasicategory F x
  have hg : g ≫ colimit.ι (rightFibrationTotalDiagram F) i = (a ≫ pullback.snd f p) ≫ p := by
    calc
      _ = (g ≫ weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ≫ f := by
        rw [Category.assoc, strictRightFibrationTotalAssembly_coefficient]
      _ = (a ≫ pullback.fst f p) ≫ f := by rw [ha]
      _ = _ := by rw [Category.assoc, pullback.condition, ← Category.assoc]
  obtain ⟨j, v, h, hh, he⟩ := exists_coslice_join_at_stage (colimit.isColimit _)
    hK i g x (a ≫ pullback.snd f p) hg
  let H := (Δ[1] ◁ g) ≫ weightedNerveTransportPrism (rightFibrationTotalDiagram F) v
  have hH : H ≫ f = (snd (Δ[1] : SSet.{u}) K ≫ a ≫ pullback.snd f p) ≫ p := by
    change ((Δ[1] ◁ g) ≫ weightedNerveTransportPrism (rightFibrationTotalDiagram F) v) ≫
      strictRightFibrationTotalAssembly F = _
    rw [Category.assoc, weightedNerveTransportPrism_assembly, ← Category.assoc,
      whiskerLeft_snd, Category.assoc, hg]
    simp only [Category.assoc]
  have h₀ : prismEndpoint 0 K ≫ H = a ≫ pullback.fst f p := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
    exact (congrArg (fun t => g ≫ t)
      (weightedNerveTransportPrism_zero (rightFibrationTotalDiagram F) v)).trans ha.symm
  have h₁ : prismEndpoint 1 K ≫ H =
      (g ≫ (rightFibrationTotalDiagram F).map v) ≫
        weightedNerveConstantLift (rightFibrationTotalDiagram F) j := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
    exact (congrArg (fun t => g ≫ t)
      (weightedNerveTransportPrism_one (rightFibrationTotalDiagram F) v)).trans
        (Category.assoc _ _ _).symm
  let P := pullbackFixedPrism f p a H hH
  let b := prismEndpoint 1 K ≫ P
  have hb : b ≫ pullback.snd f p = a ≫ pullback.snd f p :=
    pullbackFixedPrism_endpoint_snd f p a H hH 1
  have hb' : b ≫ pullback.fst f p = (joinInr Δ[0] K ≫ h) ≫
      weightedNerveConstantLift (rightFibrationTotalDiagram F) j := by
    change (prismEndpoint 1 K ≫ P) ≫ pullback.fst f p = _
    rw [Category.assoc, pullbackFixedPrism_fst, h₁, hh]
  have he' : h ≫ colimit.ι (rightFibrationTotalDiagram F) j =
      sliceUnderUncurry (b ≫ pullback.snd f p) := he.trans (congrArg sliceUnderUncurry hb.symm)
  obtain ⟨d⟩ := nonempty_coslicePullback_cocone_of_stage (Fact.out : κ.IsRegular) hK f
    (SSet.yonedaEquiv.symm x) (weightedNerveConstantLift (rightFibrationTotalDiagram F) j)
    (colimit.ι (rightFibrationTotalDiagram F) j) (strictRightFibrationTotalAssembly_coefficient F j)
    b h he' hb'
  exact nonempty_joinCocone_of_prism P (pullbackFixedPrism_zero f p a H hH h₀) rfl d

end SerrePositivity.InfinityCategories.F2.Ind
