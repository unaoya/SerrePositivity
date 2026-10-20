module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointRestrictionTotalTip
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalFamily

/-!
概要：元の左長辺族の終端係数を、上の共通余錐空間で元の全 Hom 族へ同定する。
方針：左三角形の終端辺と比較辺全体の終端を、同じ頂点制限で回収する。
規約：底への射影は取らない。使われ方：右長辺族との終端係数の厳密な比較。
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

/-- 左の終端係数は、元の Hom の普遍余錐の同じ二段制限である。 -/
lemma specifiedCoconeLeftRootTotalFamily_tip_uncurry :
    joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫
        sliceUnderUncurry (specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y) =
      pointHomLiftCone (sliceUnderProjection p) d y ≫
        (sliceUnderRestrict p i ≫ sliceUnderRestrict (i ≫ p) f) := by
  let F := specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y
  let C := specifiedCoconeLeftCommonEdgeFamily hp p c hc dB dC y
  let L := specifiedCoconeLeftFullHomFamily hp p c hc dB dC y
  have hf : joinMap (stdSimplex.δ (0 : Fin 3)) (𝟙 T) ≫ sliceUnderUncurry F =
      sliceUnderUncurry C := by
    have h := congrArg sliceUnderUncurry
      (specifiedCoconeLeftRootedHomFamily_terminal hp p c hc dB dC y)
    rw [sliceUnderUncurry_restrict, specifiedCoconeLeftTerminalHomFamily,
      sliceUnderUncurry_eqToHom
        (specifiedCoconeLeftRootedTriangle_second hp p c hc dB dC).symm] at h
    exact h
  have hC : sliceUnderUncurry C = sliceUnderUncurry L ≫ sliceUnderRestrict (i ≫ p) f := by
    rw [show C = L ≫ sliceUnderPostcomp _ (sliceUnderRestrict (i ≫ p) f) from rfl,
      sliceUnderUncurry_postcomp]
  have htip := pointRestrictionFullEdgeFamily_tip_total_uncurry
    (sliceUnderProjection p) (sliceUnderProjection (i ≫ p)) (sliceUnderRestrict p i)
    (sliceUnderRestrict_projection p i) d (specifiedCoconeLeftTransportEdge hp p c hc dB dC) y
  have hjoin {K L M : SSet.{u + 1}} (a : K ⟶ L) (b : L ⟶ M) :
      joinMap (a ≫ b) (𝟙 T) = joinMap a (𝟙 T) ≫ joinMap b (𝟙 T) := by
    simpa only [Category.comp_id] using joinMap_comp a b (𝟙 T) (𝟙 T)
  rw [specifiedCoconeLeftRootTotalFamily, sliceUnderUncurry_restrict]
  calc
    _ = joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫ sliceUnderUncurry C := by
      rw [← Category.assoc (joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T))
          (joinMap (stdSimplex.δ (1 : Fin 3)) (𝟙 T)) (sliceUnderUncurry F),
        ← joinMap_comp, Category.comp_id, ← triangleTip_longEdge, hjoin]
      simp only [Category.assoc, hf]
    _ = _ := by
      rw [hC]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ sliceUnderRestrict (i ≫ p) f) htip).trans
          (Category.assoc _ _ _))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
