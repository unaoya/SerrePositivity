module

public import SerrePositivity.KST.Spectra.RationalConstantMapping
public import SerrePositivity.KST.Spectra.TrivialFixedPointStableInjection

/-!
概要：有限群の自明作用に対する有理 Shapiro を全整数次数で証明する。
方針：通常の定数写像の高次群の全射性を BF 比較で戻し、十分高い段の自然な表示へ移す。
規約：同型の順写像は実際の標準射の誘導準同型。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有限群の有理固定点の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 有理自明作用の標準射は、BF 置換後の各段の二以上の群で全射。 -/
theorem rational_homotopyFixedPointsUnit_level_groupMap_surjective
    (G : Type u) [Group G] [Finite G] (X : OmegaSpectrum.{u}) (k r : ℕ) :
    Function.Surjective (pointedGroupMap (r + 1)
      ((homotopyFixedPointsUnit G (OmegaSpectrum.rationalization X)).app k)) := by
  let Y := OmegaSpectrum.rationalization X
  let m := (homotopyFixedPointsProjection (Action.trivial G Y)).app k ≫
    (trivialFixedPointLevelIso G Y k).hom
  let e : ((homotopyFixedPointsKan (Action.trivial G Y)).level k).space.right ≅
      (UnbasedPointedMapping.obj (nerve (AsSmall.{u} (SingleObj G))) (Y.level k).space).right :=
    PointedSimplicialSet.forget.mapIso (trivialFixedPointLevelIso G Y k)
  have hmp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism m.right :=
    (homotopyFixedPointsProjection_levelwise (Action.trivial G Y) k).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e)
  have hm : Function.Injective (pointedGroupMap (r + 1) m) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism (r + 1) m.right hmp
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint m)).injective
  have he : (homotopyFixedPointsUnit G Y).app k ≫ m =
      UnbasedPointedMapping.constant (nerve (AsSmall.{u} (SingleObj G))) (Y.level k).space :=
    homotopyFixedPointsUnit_mapping G Y k
  intro b
  obtain ⟨a, ha⟩ := RationalSkeletalTower.constant_groupMap_surjective X k G r
    (pointedGroupMap (r + 1) m b)
  refine ⟨a, hm ?_⟩
  have hc := (pointedGroupMap_comp (r + 1) ((homotopyFixedPointsUnit G Y).app k) m a).symm
  have hh := congrArg (fun f : (Y.level k).space ⟶
      UnbasedPointedMapping.obj (nerve (AsSmall.{u} (SingleObj G))) (Y.level k).space ↦
    pointedGroupMap (r + 1) f a) he
  exact hc.trans (hh.trans ha)

/-- 有限群の有理自明作用の標準射は、全整数次数のホモトピー群で全射。 -/
theorem rational_homotopyFixedPointsUnit_homotopyMap_surjective
    (G : Type u) [Group G] [Finite G] (X : OmegaSpectrum.{u}) (j : ℤ) :
    Function.Surjective (OmegaSpectrum.homotopyMap
      (homotopyFixedPointsUnit G (OmegaSpectrum.rationalization X)) j) := by
  let k := OmegaSpectrum.boundaryStage (j - 1)
  let r := OmegaSpectrum.boundaryIndex (j - 1)
  have hk : -j ≤ (k : ℤ) := by
    simpa only [k, sub_add_cancel] using OmegaSpectrum.boundaryStage_succ_admissible (j - 1)
  have hd : OmegaSpectrum.degree j k = (r + 1) + 1 := by
    simpa only [k, r, sub_add_cancel] using OmegaSpectrum.boundaryStage_succ_degree (j - 1)
  let eX := OmegaSpectrum.positiveStageEquiv (OmegaSpectrum.rationalization X) j k (r + 1) hk hd
  let eY := OmegaSpectrum.positiveStageEquiv
    (homotopyFixedPoints (Action.trivial G (OmegaSpectrum.rationalization X))) j k (r + 1) hk hd
  intro a
  obtain ⟨b, hb⟩ := rational_homotopyFixedPointsUnit_level_groupMap_surjective G X k r (eY a)
  refine ⟨eX.symm b, ?_⟩
  apply eY.injective
  rw [OmegaSpectrum.positiveStageEquiv_natural]
  change pointedGroupMap (r + 1)
    ((homotopyFixedPointsUnit G (OmegaSpectrum.rationalization X)).app k)
      (eX (eX.symm b)) = eY a
  rw [MulEquiv.apply_symm_apply]
  exact hb

/-- 有限群の有理自明作用の標準射は全整数次数の π で全単射。 -/
theorem rational_homotopyFixedPointsUnit_homotopyMap_bijective
    (G : Type u) [Group G] [Finite G] (X : OmegaSpectrum.{u}) (j : ℤ) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (homotopyFixedPointsUnit G (OmegaSpectrum.rationalization X)) j) :=
  ⟨homotopyFixedPointsUnit_homotopyMap_injective G (OmegaSpectrum.rationalization X) j,
    rational_homotopyFixedPointsUnit_homotopyMap_surjective G X j⟩

/-- 有理 Shapiro の群同型。順写像は実際の標準射の誘導準同型。 -/
def rationalShapiroEquiv (G : Type u) [Group G] [Finite G]
    (X : OmegaSpectrum.{u}) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (OmegaSpectrum.rationalization X) j ≃*
      OmegaSpectrum.homotopyGroup
        (homotopyFixedPoints (Action.trivial G (OmegaSpectrum.rationalization X))) j :=
  MulEquiv.ofBijective
    (OmegaSpectrum.homotopyMap (homotopyFixedPointsUnit G (OmegaSpectrum.rationalization X)) j)
    (rational_homotopyFixedPointsUnit_homotopyMap_bijective G X j)

end
end SerrePositivity.KST.Spectra
