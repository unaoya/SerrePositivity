module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCocone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomSpaceVertexCycle
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconePointFiberIso
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomFamilyFiberCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.CosliceInvertibleLegInitial
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomInitiality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleNerveHomotopyEquivalence

/-!
# 同じ可逆閉射を持つ bar 余錐の余極限性

## 概要
正規化 bar からの閉射が H⁰ で可逆なら、その同じ指定閉射の余錐は余極限。

## 方針
一点比較の実際の脚の cycle を保持し、左ファイブレーションの Hom 判定で始対象性を戻す。

## 規約
余錐空間同型で指定済みの同じ余錐を用いる。

## 使われ方
HA 1.2.4、Kerodon 7.1（Tag 02H1）。同じ実現比較を持つ余錐の検収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Opposite SSet SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (N : RightModule R D)
  (f : ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D F) ⟶
    ForgetEnrichment.of (Complex R) N)

/-- 一点比較へ送った同じ余錐の脚は、最初に指定した閉射の cycle を持つ。 -/
theorem dgCoherentBarClosedMapCoconePoint_leg_cycle :
    let hMC := dgCoherentBarMaurerCartan_unconditional R D F
    let c := dgCoherentBarClosedMapCoconePoint R D F N f
    edgeCycle (cosliceFiberVertexToEdge
      ((dgCoherentBarCoconePointFiber R D F hMC (Simplex.vertex N)).app (op ⦋0⦌) c)).toTruncated =
        (closedHomEquiv R (RightModule R D) _ _) f := by
  let hMC := dgCoherentBarMaurerCartan_unconditional R D F
  let c := dgCoherentBarClosedMapCoconePoint R D F N f
  let d := (dgCoherentBarCoconePointFiber R D F hMC (Simplex.vertex N)).app (op ⦋0⦌) c
  have hc := ConcreteCategory.congr_hom
    (NatTrans.congr_app (dgCoherentBarCoconePointFiber_comparison R D F hMC (Simplex.vertex N))
      (op ⦋0⦌)) c
  have hh := congrArg (PinchedHom.vertexCycleEquiv (dgCoherentBarNormalizedModule R D F hMC) N) hc
  have hz := hh.trans (dgCoherentBarClosedMapCoconePoint_cycle R D F N f)
  apply Subtype.ext
  exact (dgCoherentBarPointHomSpaceIso_vertexCycle R D F hMC N d).symm.trans
    (congrArg Subtype.val hz)

/-- H⁰ で可逆な指定閉射から戻した同じ余錐は、実際の余極限余錐。 -/
theorem dgCoherentBarClosedMapCocone_isColimit
    (hf : IsIso ((moduleToHomotopy R D).map f)) :
    IsColimitCone (dgCoherentBarClosedMapCocone R D F N f) := by
  let hMC := dgCoherentBarMaurerCartan_unconditional R D F
  let c := dgCoherentBarClosedMapCoconePoint R D F N f
  let d := (dgCoherentBarCoconePointFiber R D F hMC (Simplex.vertex N)).app (op ⦋0⦌) c
  let e := (cosliceFiberVertexToEdge d).toTruncated
  have he : (edgeClosedEquiv (Simplex.vertex (dgCoherentBarNormalizedModule R D F hMC))
      (Simplex.vertex N)) e = f := by
    apply (closedHomEquiv R (RightModule R D) _ _).injective
    change (unitCycleEquiv _) ((unitCycleEquiv _).symm (edgeCycle e)) = _
    rw [Equiv.apply_symm_apply]
    exact dgCoherentBarClosedMapCoconePoint_leg_cycle R D F N f
  have h₂ : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) := by
    let H := toH0 R (RightModule R D)
    have : IsIso (H.map (SSet.Truncated.HomotopyCategory₂.homMk e)) := by
      rw [toH0_homMk]
      have he' : SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e = f := he
      rw [he']
      exact hf
    exact isIso_of_reflects_iso _ H
  have h₁ : IsInvertibleEdge e :=
    (SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk e)
  let dc : JoinCocone (SSet.yonedaEquiv.symm (dgCoherentBarNativeApex R D F hMC)) := d.val
  have hd : IsInitialVertex (X := sliceUnder (SSet.yonedaEquiv.symm (dgCoherentBarNativeApex R D F hMC))) dc := by
    apply coslice_isInitialVertex_of_invertible_leg _ dc
    apply (isInvertibleEdge_congr (e := dc.leg (𝟙 Δ[0])) (f := e) ?_).mpr h₁
    change SSet.yonedaEquiv (_ ≫ joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ dc.val) = _
    rw [joinMap_id, Category.id_comp]
    rfl
  apply (isColimitCone_iff_coconePointHomFamily_homotopyEquivalence _).mpr
  intro y
  exact dgCoherentBarPointHomFamily_equivalence_of_fiberComparison
    (sliceUnderProjection F)
    (sliceUnderProjection (SSet.yonedaEquiv.symm (dgCoherentBarNativeApex R D F hMC)))
    (dgCoherentBarCoconePointComparison R D F hMC)
    (dgCoherentBarCoconePointComparison_projection R D F hMC) c.val dc rfl hd y
    (dgCoherentBarCoconePointFiber_homotopyEquivalence R D F hMC y).isQCatEquivalence

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
