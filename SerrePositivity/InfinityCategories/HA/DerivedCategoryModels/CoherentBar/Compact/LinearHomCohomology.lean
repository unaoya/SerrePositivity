module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.LinearLiftPiCharts
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.StandardPiCohomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.OppositePiZeroComparison
/-!
概要：coslice 比較の線形 Hom 模型に全基点のコホモロジーチャートを与える。
方針：二回の宇宙持ち上げと反転の零基点比較を、加法平行移動で全基点へ延長する。
規約：元の鎖写像の作用と任意指定道を同時に保持する。
使われ方：同じ native 評価余錐の π 条件を実ホモロジー余極限から導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology DifferentialGraded HomologicalComplex
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

local instance (x y : D) : SSet.KanComplex
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpaceKan x y
local instance (a b : E) : SSet.KanComplex
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) a b)) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpaceKan a b

/-- 実 coslice 比較の始域を線形化した加群。 -/
def dgBarCompactLinearHomModule (x y : D) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLiftModule.{u, max u v, max u v + 1}
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLiftModule.{u, u, v}
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositeModule (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)))

instance dgBarCompactLinearHomModule_kan (x y : D) :
    SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)) := by
  dsimp only [dgBarCompactLinearHomModule]
  infer_instance

/-- 元の鎖写像が全線形模型へ与える実射。 -/
def dgBarCompactLinearHomCohomologyMap
    (φ : homObject R D x y ⟶ homObject R E a b) :
    dgBarCompactLinearHomModule (R := R) x y ⟶ dgBarCompactLinearHomModule (R := R) a b :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLiftModuleMap.{u, max u v, max u v + 1}
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLiftModuleMap.{u, u, v}
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositeModuleMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ)))

/-- 零基点のコホモロジーチャート。 -/
def dgBarCompactLinearHomZeroBaseCohomologyEquiv (x y : D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)) n 0 ≃*
      Multiplicative ((homObject R D x y).homology (-((n + 1 : ℕ) : ℤ))) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLiftModulePiZeroBaseEquiv _ n).trans
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLiftModulePiZeroBaseEquiv _ n).trans
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositeModulePiZeroBaseEquiv _ n).trans
        ((_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.modulePiMooreGroupEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) n).trans
          (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.additiveGroupToMultiplicativeEquiv
            (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardMooreCohomologyIso x y (n + 1)).toLinearEquiv.toAddEquiv))))

lemma dgBarCompactLinearHomZeroBaseCohomologyEquiv_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) (n : ℕ)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)) n 0) :
    dgBarCompactLinearHomZeroBaseCohomologyEquiv a b n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (dgBarCompactLinearHomCohomologyMap φ))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero (dgBarCompactLinearHomCohomologyMap φ)) α) =
      homologyMap φ (-((n + 1 : ℕ) : ℤ))
        (dgBarCompactLinearHomZeroBaseCohomologyEquiv x y n α) := by
  dsimp only [dgBarCompactLinearHomCohomologyMap, dgBarCompactLinearHomModule] at *
  dsimp only [dgBarCompactLinearHomZeroBaseCohomologyEquiv, MulEquiv.trans_apply]
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLiftModulePiZeroBaseEquiv_naturality,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLiftModulePiZeroBaseEquiv_naturality,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositeModulePiZeroBaseEquiv_naturality,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiMooreGroupEquiv_naturality]
  exact ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardMooreCohomologyIso_naturality φ (n + 1)) _

/-- 指定した任意の基点の正次数チャート。 -/
def dgBarCompactLinearHomPiCohomologyEquiv (x y : D) (n : ℕ)
    (z : (dgBarCompactLinearHomModule (R := R) x y).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)) n z ≃
      (homObject R D x y).homology (-((n + 1 : ℕ) : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleZeroChartExtension n
    (dgBarCompactLinearHomZeroBaseCohomologyEquiv x y n).toEquiv z

lemma dgBarCompactLinearHomPiCohomologyEquiv_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) (n : ℕ)
    (z : (dgBarCompactLinearHomModule (R := R) x y).obj (Opposite.op ⦋0⦌))
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)) n z) :
    dgBarCompactLinearHomPiCohomologyEquiv a b n
      ((dgBarCompactLinearHomCohomologyMap φ).app _ z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (dgBarCompactLinearHomCohomologyMap φ)) z α) =
      homologyMap φ (-((n + 1 : ℕ) : ℤ))
        (dgBarCompactLinearHomPiCohomologyEquiv x y n z α) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleZeroChartExtension_naturality (dgBarCompactLinearHomCohomologyMap φ) n
    (dgBarCompactLinearHomZeroBaseCohomologyEquiv x y n).toEquiv
    (dgBarCompactLinearHomZeroBaseCohomologyEquiv a b n).toEquiv _
    (dgBarCompactLinearHomZeroBaseCohomologyEquiv_naturality φ n) z α

lemma dgBarCompactLinearHomPiCohomologyEquiv_transport (x y : D) (n : ℕ)
    {z z' : (dgBarCompactLinearHomModule (R := R) x y).obj (Opposite.op ⦋0⦌)}
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)).Edge z z')
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)) n z)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)) n z')
    (h : dgBarCompactLinearHomPiCohomologyEquiv x y n z a =
      dgBarCompactLinearHomPiCohomologyEquiv x y n z' b) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleZeroChartExtension_transport n _ e a b h

/-- 同じ線形模型の零次数チャート。 -/
def dgBarCompactLinearHomPiZeroCohomologyEquiv (x y : D) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y)) ≃
      (homObject R D x y).homology 0 :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiZeroEquiv.{max u v, max u v + 1}
    ((SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y).op)).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiZeroEquiv.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y).op).symm.trans
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositePiZeroEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y)).trans
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardPiZeroCohomologyEquiv x y)))

lemma dgBarCompactLinearHomPiZeroCohomologyEquiv_naturality
    (φ : homObject R D x y ⟶ homObject R E a b)
    (α : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y))) :
    dgBarCompactLinearHomPiZeroCohomologyEquiv a b
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (dgBarCompactLinearHomCohomologyMap φ)) α) =
      homologyMap φ 0 (dgBarCompactLinearHomPiZeroCohomologyEquiv x y α) := by
  obtain ⟨z, rfl⟩ := SSet.π₀.mk_surjective α
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardPiZeroCohomologyEquiv_naturality φ
    (SSet.π₀.mk (SSet.opObjEquiv z.down.down))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
