module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EdgewisePiNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleZeroChartExtension
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology Opposite SSet HomotopyLimits
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]

/-- 係数の反転模型。 -/
def dgBarCompactOppositeModule (W : SimplicialObject (ModuleCat.{v} R)) :=
  SimplicialObject.opFunctor.obj W

/-- 係数の宇宙持ち上げ模型。 -/
def dgBarCompactLiftModule (W : SimplicialObject (ModuleCat.{v} R)) :=
  W ⋙ ModuleCat.uliftFunctor.{w} R

instance dgBarCompactOppositeModule_kan (W : SimplicialObject (ModuleCat.{v} R))
    [KanComplex (moduleUnderlyingSSet W)] :
    KanComplex (moduleUnderlyingSSet (dgBarCompactOppositeModule W)) := by
  change KanComplex (moduleUnderlyingSSet W).op
  infer_instance

instance dgBarCompactLiftModule_kan (W : SimplicialObject (ModuleCat.{v} R))
    [KanComplex (moduleUnderlyingSSet W)] :
    KanComplex (moduleUnderlyingSSet (dgBarCompactLiftModule.{u, v, w} W)) := by
  change KanComplex ((SSet.uliftFunctor.{w, v}).obj (moduleUnderlyingSSet W))
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
    (W : SimplicialObject (ModuleCat.{v} R)) [KanComplex (moduleUnderlyingSSet W)] (n : ℕ) :
    KanHomotopyGroup (moduleUnderlyingSSet (dgBarCompactOppositeModule W)) n 0 ≃*
      KanHomotopyGroup (moduleUnderlyingSSet W) n 0 :=
  dgBarCompactOppositePiEquiv (moduleUnderlyingSSet W) n 0

/-- 零基点を保持する宇宙比較。 -/
def dgBarCompactLiftModulePiZeroBaseEquiv
    (W : SimplicialObject (ModuleCat.{v} R)) [KanComplex (moduleUnderlyingSSet W)] (n : ℕ) :
    KanHomotopyGroup (moduleUnderlyingSSet (dgBarCompactLiftModule.{u, v, w} W)) n 0 ≃*
      KanHomotopyGroup (moduleUnderlyingSSet W) n 0 :=
  (dgBarCompactUliftPiEquiv.{v, w} (moduleUnderlyingSSet W) n 0).symm

lemma dgBarCompactOppositePiEquiv_naturality_of_eq
    {X Y : SSet.{v}} [KanComplex X] [KanComplex Y] (φ : X ⟶ Y) (n : ℕ)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (hy : φ.app _ x = y)
    (a : KanHomotopyGroup X.op n (SSet.opObjEquiv.symm x)) :
    dgBarCompactOppositePiEquiv Y n y
      (KanHomotopyGroup.map (x := SSet.opObjEquiv.symm x)
        (y := SSet.opObjEquiv.symm y) (SSet.opFunctor.map φ)
        (congrArg SSet.opObjEquiv.symm hy) a) =
      KanHomotopyGroup.map φ hy (dgBarCompactOppositePiEquiv X n x a) := by
  subst y
  exact dgBarCompactOppositePiEquiv_naturality φ n x a

lemma dgBarCompactOppositeModulePiZeroBaseEquiv_naturality
    {W V : SimplicialObject (ModuleCat.{v} R)}
    [KanComplex (moduleUnderlyingSSet W)] [KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) (n : ℕ)
    (a : KanHomotopyGroup (moduleUnderlyingSSet (dgBarCompactOppositeModule W)) n 0) :
    dgBarCompactOppositeModulePiZeroBaseEquiv V n
      (KanHomotopyGroup.map (moduleUnderlyingSSetMap (dgBarCompactOppositeModuleMap f))
        (moduleUnderlyingSSetMap_zero (dgBarCompactOppositeModuleMap f)) a) =
      KanHomotopyGroup.map (moduleUnderlyingSSetMap f) (moduleUnderlyingSSetMap_zero f)
        (dgBarCompactOppositeModulePiZeroBaseEquiv W n a) :=
  dgBarCompactOppositePiEquiv_naturality_of_eq (moduleUnderlyingSSetMap f) n
    (moduleUnderlyingSSetMap_zero f) a

lemma dgBarCompactUliftPiEquiv_naturality_of_eq
    {X Y : SSet.{v}} [KanComplex X] [KanComplex Y] (φ : X ⟶ Y) (n : ℕ)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (hy : φ.app _ x = y)
    (a : KanHomotopyGroup X n x) :
    dgBarCompactUliftPiEquiv.{v, w} Y n y (KanHomotopyGroup.map φ hy a) =
      KanHomotopyGroup.map (x := ULift.up x) (y := ULift.up y)
        ((SSet.uliftFunctor.{w, v}).map φ) (congrArg ULift.up hy)
        (dgBarCompactUliftPiEquiv.{v, w} X n x a) := by
  induction a using Quotient.inductionOn with | h f => ?_
  apply congrArg KanHomotopyGroup.mk
  apply RelativeMorphism.ext
  change (uliftStdSimplexIso.{v, w} (n + 1)).inv ≫
    (SSet.uliftFunctor.{w, v}).map (f.map ≫ φ) =
      ((uliftStdSimplexIso.{v, w} (n + 1)).inv ≫
        (SSet.uliftFunctor.{w, v}).map f.map) ≫ (SSet.uliftFunctor.{w, v}).map φ
  rw [Functor.map_comp, Category.assoc]

lemma dgBarCompactLiftModulePiZeroBaseEquiv_naturality
    {W V : SimplicialObject (ModuleCat.{v} R)}
    [KanComplex (moduleUnderlyingSSet W)] [KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) (n : ℕ)
    (a : KanHomotopyGroup (moduleUnderlyingSSet (dgBarCompactLiftModule.{u, v, w} W)) n 0) :
    dgBarCompactLiftModulePiZeroBaseEquiv V n
      (KanHomotopyGroup.map (moduleUnderlyingSSetMap (dgBarCompactLiftModuleMap f))
        (moduleUnderlyingSSetMap_zero (dgBarCompactLiftModuleMap f)) a) =
      KanHomotopyGroup.map (moduleUnderlyingSSetMap f) (moduleUnderlyingSSetMap_zero f)
        (dgBarCompactLiftModulePiZeroBaseEquiv W n a) := by
  obtain ⟨a₀, rfl⟩ :=
    (dgBarCompactUliftPiEquiv.{v, w} (moduleUnderlyingSSet W) n 0).surjective a
  have h := dgBarCompactUliftPiEquiv_naturality_of_eq.{v, w}
    (moduleUnderlyingSSetMap f) n (moduleUnderlyingSSetMap_zero f) a₀
  change (dgBarCompactUliftPiEquiv.{v, w} (moduleUnderlyingSSet V) n 0).symm
    (KanHomotopyGroup.map (moduleUnderlyingSSetMap (dgBarCompactLiftModuleMap f))
      (moduleUnderlyingSSetMap_zero (dgBarCompactLiftModuleMap f))
      ((dgBarCompactUliftPiEquiv.{v, w} (moduleUnderlyingSSet W) n 0) a₀)) = _
  have h' := congrArg (dgBarCompactUliftPiEquiv.{v, w}
    (moduleUnderlyingSSet V) n 0).symm h.symm
  calc
    _ = KanHomotopyGroup.map (moduleUnderlyingSSetMap f)
        (moduleUnderlyingSSetMap_zero f) a₀ :=
      h'.trans ((dgBarCompactUliftPiEquiv.{v, w} (moduleUnderlyingSSet V) n 0).symm_apply_apply _)
    _ = _ := congrArg
      (KanHomotopyGroup.map (moduleUnderlyingSSetMap f) (moduleUnderlyingSSetMap_zero f))
      ((dgBarCompactUliftPiEquiv.{v, w} (moduleUnderlyingSSet W) n 0).symm_apply_apply a₀).symm

end SerrePositivity.InfinityCategories
