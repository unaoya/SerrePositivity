module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayIso
public import SerrePositivity.KST.SConstruction.CubicalDayRepresentable
public import SerrePositivity.KST.SConstruction.CubicalDayTensorLaws

/-! # 元の Serre 生成射の tensor 比較
概要：元の二つの Yoneda 生成射の tensor を、元の Day 連結生成射へ戻す。
方針：元の cell 組み立てと cotensorator の逆律を使う。
規約：元の全鎖射と連結 cell を保持。使われ方：necklace の実 Serre 合成の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Yoneda 生成射は、同じ元の cell の Serre 射そのもの。 -/
lemma cubicalSerreGenerator_eq_cell {K : CubicalSet.{u}} {c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (φ : cubicalYoneda.obj c ⟶ K) :
    cubicalSerreGenerator A φ = cubicalSerreCell A c (uliftYonedaEquiv φ) := by
  change _ = (cubicalSerreChainsCubeUnit A).app c ≫
    (cubicalSerreChains A).map (uliftYonedaEquiv.symm (uliftYonedaEquiv φ))
  erw [Equiv.symm_apply_apply]
  rfl

/-- 元の両表現可能生成射を連結すると、同じ元の二つの cell の Day 生成射になる。 -/
lemma cubicalDayCubeInclusion_tensor {K L : CubicalSet.{u}} {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (φ : cubicalYoneda.obj c ⟶ K) (ψ : cubicalYoneda.obj d ⟶ L) :
    cubicalDayCubeInclusion c d ≫ cubicalDayTensorMap φ ψ =
      cubicalCell (concreteCubeTensorObj c d)
        (cubicalDayTensorCell c d (uliftYonedaEquiv φ) (uliftYonedaEquiv ψ)) := by
  apply uliftYonedaEquiv.injective
  erw [uliftYonedaEquiv_comp]
  change (cubicalDayTensorMap φ ψ).app (op (concreteCubeTensorObj c d))
    (uliftYonedaEquiv (uliftYonedaEquiv.symm
      (cubicalDayTensorCell c d (ULift.up (𝟙 c)) (ULift.up (𝟙 d))))) = _
  erw [Equiv.apply_symm_apply, cubicalDayTensorMap_cell]
  exact (Equiv.apply_symm_apply _ _).symm

/-- 元の Serre 分割と二つの生成射の tensor は、元の連結 Day 生成射を回収する。 -/
lemma cubicalSerreGenerator_tensor {K L : CubicalSet.{u}} {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (φ : cubicalYoneda.obj c ⟶ K) (ψ : cubicalYoneda.obj d ⟶ L) :
    Functor.OplaxMonoidal.δ (serreConcreteCubeComplexFunctor A) c d ≫
      (cubicalSerreGenerator A φ ⊗ₘ cubicalSerreGenerator A ψ) ≫
        cubicalSerreDayInverse A K L =
      cubicalSerreGenerator A (cubicalDayCubeInclusion c d ≫ cubicalDayTensorMap φ ψ) := by
  rw [cubicalSerreGenerator_eq_cell, cubicalSerreGenerator_eq_cell,
    cubicalSerreDayInverse_cell, cubicalSerreDayAssembly_cotensorator,
    cubicalDayCubeInclusion_tensor]
  rfl

end SerrePositivity.KST.SConstruction
