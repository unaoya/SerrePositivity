module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EdgewisePiNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleZeroChartExtension
/-!
概要：反転・宇宙持ち上げを施した単体的加群の零基点 π チャート。
方針：同じ基点の宇宙比較と edgewise 比較を合成する。
規約：実線形射を保持し、零基点の像の等式を明示する。
使われ方：coslice の線形模型を全基点の native コホモロジーチャートへ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology Opposite SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]

/-- 係数の反転模型。 -/
def dgBarCompactOppositeModule (W : SimplicialObject (ModuleCat.{v} R)) :=
  SimplicialObject.opFunctor.obj W

/-- 係数の宇宙持ち上げ模型。 -/
def dgBarCompactLiftModule (W : SimplicialObject (ModuleCat.{v} R)) :=
  W ⋙ ModuleCat.uliftFunctor.{w} R

instance dgBarCompactOppositeModule_kan (W : SimplicialObject (ModuleCat.{v} R))
    [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactOppositeModule W)) := by
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).op
  infer_instance

instance dgBarCompactLiftModule_kan (W : SimplicialObject (ModuleCat.{v} R))
    [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLiftModule.{u, v, w} W)) := by
  change KanComplex ((SSet.uliftFunctor.{w, v}).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W))
  infer_instance

/-- 実線形射の反転。 -/
def dgBarCompactOppositeModuleMap {W V : SimplicialObject (ModuleCat.{v} R)} (f : W ⟶ V) :
    dgBarCompactOppositeModule W ⟶ dgBarCompactOppositeModule V :=
  SimplicialObject.opFunctor.map f

/-- 実線形射の宇宙持ち上げ。 -/
def dgBarCompactLiftModuleMap {W V : SimplicialObject (ModuleCat.{v} R)} (f : W ⟶ V) :
    dgBarCompactLiftModule.{u, v, w} W ⟶ dgBarCompactLiftModule.{u, v, w} V :=
  Functor.whiskerRight f (ModuleCat.uliftFunctor.{w} R)

/-- 零基点を保持する反転比較。 -/
def dgBarCompactOppositeModulePiZeroBaseEquiv
    (W : SimplicialObject (ModuleCat.{v} R)) [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactOppositeModule W)) n 0 ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0 :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositePiEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0

/-- 零基点を保持する宇宙比較。 -/
def dgBarCompactLiftModulePiZeroBaseEquiv
    (W : SimplicialObject (ModuleCat.{v} R)) [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLiftModule.{u, v, w} W)) n 0 ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0 :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0).symm

lemma dgBarCompactOppositePiEquiv_naturality_of_eq
    {X Y : SSet.{v}} [KanComplex X] [KanComplex Y] (φ : X ⟶ Y) (n : ℕ)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (hy : φ.app _ x = y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.op n (SSet.opObjEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositePiEquiv Y n y
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (x := SSet.opObjEquiv.symm x)
        (y := SSet.opObjEquiv.symm y) (SSet.opFunctor.map φ)
        (congrArg SSet.opObjEquiv.symm hy) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hy (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositePiEquiv X n x a) := by
  subst y
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositePiEquiv_naturality φ n x a

lemma dgBarCompactOppositeModulePiZeroBaseEquiv_naturality
    {W V : SimplicialObject (ModuleCat.{v} R)}
    [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V)]
    (f : W ⟶ V) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactOppositeModule W)) n 0) :
    dgBarCompactOppositeModulePiZeroBaseEquiv V n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (dgBarCompactOppositeModuleMap f))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero (dgBarCompactOppositeModuleMap f)) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f)
        (dgBarCompactOppositeModulePiZeroBaseEquiv W n a) :=
  dgBarCompactOppositePiEquiv_naturality_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f) a

lemma dgBarCompactUliftPiEquiv_naturality_of_eq
    {X Y : SSet.{v}} [KanComplex X] [KanComplex Y] (φ : X ⟶ Y) (n : ℕ)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (hy : φ.app _ x = y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w} Y n y (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hy a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (x := ULift.up x) (y := ULift.up y)
        ((SSet.uliftFunctor.{w, v}).map φ) (congrArg ULift.up hy)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w} X n x a) := by
  induction a using Quotient.inductionOn with | h f => ?_
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
  apply RelativeMorphism.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{v, w} (n + 1)).inv ≫
    (SSet.uliftFunctor.{w, v}).map (f.map ≫ φ) =
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{v, w} (n + 1)).inv ≫
        (SSet.uliftFunctor.{w, v}).map f.map) ≫ (SSet.uliftFunctor.{w, v}).map φ
  rw [Functor.map_comp, Category.assoc]

lemma dgBarCompactLiftModulePiZeroBaseEquiv_naturality
    {W V : SimplicialObject (ModuleCat.{v} R)}
    [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V)]
    (f : W ⟶ V) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (dgBarCompactLiftModule.{u, v, w} W)) n 0) :
    dgBarCompactLiftModulePiZeroBaseEquiv V n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (dgBarCompactLiftModuleMap f))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero (dgBarCompactLiftModuleMap f)) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f)
        (dgBarCompactLiftModulePiZeroBaseEquiv W n a) := by
  obtain ⟨a₀, rfl⟩ :=
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0).surjective a
  have h := dgBarCompactUliftPiEquiv_naturality_of_eq.{v, w}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f) a₀
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V) n 0).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (dgBarCompactLiftModuleMap f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero (dgBarCompactLiftModuleMap f))
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0) a₀)) = _
  have h' := congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V) n 0).symm h.symm
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f) a₀ :=
      h'.trans ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V) n 0).symm_apply_apply _)
    _ = _ := congrArg
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f))
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{v, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0).symm_apply_apply a₀).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
