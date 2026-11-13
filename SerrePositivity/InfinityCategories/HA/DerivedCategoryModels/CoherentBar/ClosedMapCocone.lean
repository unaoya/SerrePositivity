module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Unconditional
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomSpaceIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom

/-!
# 正規化 bar からの指定閉射に対応する同じ終点の余錐

## 概要
既存の native bar の Hom 空間同型を逆向きに使い、指定した閉射の余錐を取る。

## 方針
閉零射を pinched Hom の零単体へ移し、既存の余錐空間同型の逆を適用する。

## 規約
HA の join 方程式や native 余錐を新しく構成しない。終点は同じ指定加群。

## 使われ方
HA 1.2.4、Kerodon 7.1（Tag 02H1）。計算済みの同じ比較射への余錐の輸送。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (N : RightModule R D)
  (f : ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D F) ⟶
    ForgetEnrichment.of (Complex R) N)

/-- 指定閉射を、同じ終点に固定した既存の余錐空間同型で戻した零単体。 -/
def dgCoherentBarClosedMapCoconePoint :
    (coconeMappingSpace F (Simplex.vertex N)) _⦋0⦌ :=
  (dgCoherentBarCoconeHomSpaceIsoUnconditional R D F (Simplex.vertex N)).inv.app (op ⦋0⦌)
    ((PinchedHom.vertexCycleEquiv (dgCoherentBarNormalizedModuleUnconditional R D F) N).symm
      ((closedHomEquiv R (RightModule R D) _ _) f))

/-- 同じ指定閉射から得る、全高次成分を持つ実際の join 余錐。 -/
def dgCoherentBarClosedMapCocone : JoinCocone F := (dgCoherentBarClosedMapCoconePoint R D F N f).val

/-- この余錐の頂点は指定した同じ加群である。 -/
theorem dgCoherentBarClosedMapCocone_vertex :
    (dgCoherentBarClosedMapCocone R D F N f).vertex = Simplex.vertex N := by
  have h := (dgCoherentBarClosedMapCoconePoint R D F N f).property
  exact h.trans (constant_zero (X := dgNerve R (RightModule R D)) (Simplex.vertex N))

/-- Hom 空間へ戻すと、最初に指定した閉零射の cycle そのものになる。 -/
theorem dgCoherentBarClosedMapCoconePoint_cycle :
    PinchedHom.vertexCycleEquiv (dgCoherentBarNormalizedModuleUnconditional R D F) N
      ((dgCoherentBarCoconeHomSpaceIsoUnconditional R D F (Simplex.vertex N)).hom.app (op ⦋0⦌)
        (dgCoherentBarClosedMapCoconePoint R D F N f)) =
      (closedHomEquiv R (RightModule R D) _ _) f := by
  let e := dgCoherentBarCoconeHomSpaceIsoUnconditional R D F (Simplex.vertex N)
  let z := (PinchedHom.vertexCycleEquiv (dgCoherentBarNormalizedModuleUnconditional R D F) N).symm
    ((closedHomEquiv R (RightModule R D) _ _) f)
  have h := ConcreteCategory.congr_hom (Iso.inv_hom_id_app e (op ⦋0⦌)) z
  exact (congrArg
    (PinchedHom.vertexCycleEquiv (dgCoherentBarNormalizedModuleUnconditional R D F) N) h).trans
      ((PinchedHom.vertexCycleEquiv (dgCoherentBarNormalizedModuleUnconditional R D F) N).apply_symm_apply _)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
