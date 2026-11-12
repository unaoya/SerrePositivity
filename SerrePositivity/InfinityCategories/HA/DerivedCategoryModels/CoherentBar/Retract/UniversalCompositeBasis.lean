module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalLabelCoefficients
/-!
概要：標準単体の恒等基底への二つの単体写像の作用は、合成ラベルの基底となる。
方針：自由加群の基底への写像則を二回使い、標準単体の点で比較する。
規約：単体写像の向きと三つの次元を保持する。
使われ方：Hσ の普遍係数を単体自己写像の有限係数和として評価する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]

lemma dgCoherentBarUniversalComposite_basis {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋l⦌ ⟶ ⦋m⦌) :
    ((ModuleCat.free R).map ((Δ[n] : SSet.{u}).map g.op)).hom
      (((ModuleCat.free R).map ((Δ[n] : SSet.{u}).map f.op)).hom
        (ModuleCat.freeMk (R := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n))) =
    ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm (g ≫ f)) := by
  change (ModuleCat.free R).map ((Δ[n] : SSet.{u}).map g.op)
    ((ModuleCat.free R).map ((Δ[n] : SSet.{u}).map f.op)
      (ModuleCat.freeMk (R := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n))) = _
  rw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  congr 1

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
