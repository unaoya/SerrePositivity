module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRootTotalTip
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalEnd

/-!
概要：元の右長辺族の終端係数を回収し、左長辺族の終端と上の空間で照合する。
方針：右四面体の終端面・修正三角形の長辺・元の比較辺を同じ頂点で制限する。
規約：全 Hom の族の厳密な等式。使われ方：相対 coslice 制限の両端係数の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => pinchedHomLeft (JoinCocone.vertex d) y

/-- 右の終端係数も、元の Hom の普遍余錐の同じ二段制限である。 -/
lemma specifiedCoconeRightRootTotalFamily_tip_uncurry :
    joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫
        sliceUnderUncurry (specifiedCoconeRightRootTotalFamily hp p c hc dB dC y) =
      pointHomLiftCone (sliceUnderProjection p) d y ≫
        (sliceUnderRestrict p j ≫
          normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)) := by
  let F := specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y
  let C := specifiedCoconeCommonHomTriangleFamily hp p c hc dB dC y
  let R := specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y
  let L := specifiedCoconeRightFullHomFamily hp p c hc dB dC y
  let r := normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)
  have hf : joinMap (stdSimplex.δ (0 : Fin 4)) (𝟙 T) ≫ sliceUnderUncurry F =
      sliceUnderUncurry C := by
    have h := congrArg sliceUnderUncurry
      (specifiedCoconeRootedHomTetrahedronFamily_terminalFace hp p c hc dB dC y)
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_eqToHom
      (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC).symm] at h
    exact h
  have hl : joinMap (stdSimplex.δ (1 : Fin 3)) (𝟙 T) ≫ sliceUnderUncurry R =
      sliceUnderUncurry L := by
    have h := congrArg sliceUnderUncurry
      (specifiedCoconeRightHomTriangleFamily_longEdge hp p c hc dB dC y)
    rw [sliceUnderUncurry_restrict, specifiedCoconeRightHomLongEdgeFamily,
      sliceUnderUncurry_eqToHom
        (specifiedCoconeRightTriangle_longEdge hp p c hc dB dC).symm] at h
    exact h
  have hC : sliceUnderUncurry C = sliceUnderUncurry R ≫ r := by
    rw [show C = R ≫ sliceUnderPostcomp _ r from rfl, sliceUnderUncurry_postcomp]
  have hla := congrArg (fun k ↦ k ≫ r) hl
  simp only [Category.assoc] at hla
  have htip := pointRestrictionFullEdgeFamily_tip_total_uncurry
    (sliceUnderProjection p) (sliceUnderProjection (j ≫ p)) (sliceUnderRestrict p j)
    (sliceUnderRestrict_projection p j) d (specifiedCoconeBranchData hp p c hc dB dC).right y
  have hjoin {K L M : SSet.{u + 1}} (a : K ⟶ L) (b : L ⟶ M) :
      joinMap (a ≫ b) (𝟙 T) = joinMap a (𝟙 T) ≫ joinMap b (𝟙 T) := by
    simpa only [Category.comp_id] using joinMap_comp a b (𝟙 T) (𝟙 T)
  rw [specifiedCoconeRightRootTotalFamily, sliceUnderUncurry_restrict]
  calc
    _ = joinMap (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) (𝟙 T) ≫
        sliceUnderUncurry C := by
      rw [← Category.assoc (joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T))
          (joinMap tetrahedronRootEdge (𝟙 T)) (sliceUnderUncurry F),
        ← joinMap_comp, Category.comp_id,
        tetrahedronRootEdge_target_terminalFace, hjoin]
      simp only [Category.assoc, hf]
    _ = joinMap (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) (𝟙 T) ≫
        (sliceUnderUncurry R ≫ r) := congrArg (fun k ↦ _ ≫ k) hC
    _ = joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫ (sliceUnderUncurry L ≫ r) := by
      rw [triangleTip_longEdge, hjoin]
      simp only [Category.assoc, hla]
    _ = _ := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ r) htip).trans (Category.assoc _ _ _))

/-- 元の左右の全長辺族の終端係数は、上の余錐空間で厳密に一致する。 -/
lemma specifiedCoconeRootTotalFamilies_tip_uncurry :
    joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫
        sliceUnderUncurry (specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y) =
      joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫
        sliceUnderUncurry (specifiedCoconeRightRootTotalFamily hp p c hc dB dC y) := by
  rw [specifiedCoconeLeftRootTotalFamily_tip_uncurry,
    specifiedCoconeRightRootTotalFamily_tip_uncurry]
  exact congrArg (fun k ↦ pointHomLiftCone (sliceUnderProjection p) d y ≫ k)
    (cosliceShapePushout_comm hp p)

/-- 円柱の時間一の端面と元の右族は、上の終端係数が厳密に一致する。 -/
lemma specifiedCoconeRootVerticalEndFamily_right_terminal :
    specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫
        sliceUnderRestrict
          (tetrahedronRootEdge ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
          (stdSimplex.δ (0 : Fin 2)) =
      specifiedCoconeRightRootTotalFamily hp p c hc dB dC y ≫
        sliceUnderRestrict
          (tetrahedronRootEdge ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
          (stdSimplex.δ (0 : Fin 2)) := by
  apply sliceUnderUncurry_injective _
  rw [specifiedCoconeRootVerticalEndFamily_terminal, normalizedCoconeRestriction_uncurry,
    sliceUnderUncurry_restrict]
  exact specifiedCoconeRootTotalFamilies_tip_uncurry hp p c hc dB dC y

end
end SerrePositivity.InfinityCategories.HomotopyLimits
