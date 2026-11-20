module

public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBoundaryTorsion
public import SerrePositivity.AlgebraicGeometry.TensorPureTransformBaseChange
public import SerrePositivity.AlgebraicGeometry.FlatPureTransformBaseChangeOfBound

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の有限型代数上有限な加群のチャート上の平坦性の安定性。
方針：基底変更代数上の Noether 性で一様なねじれの指数を選び、二段の純変換を打ち消す。
規約：元の加群は B 上有限でよく、R 上有限とは仮定しない。
使われ方：一般の有限型特殊形における局所平坦化の共通細分。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：有限型代数上有限な加群のチャートで平坦な純変換は追加の係数拡大後にも平坦。
方針：チャート上の境界ねじれの一様消滅から追加基底変更を比較し、元の基礎環の形に戻す。
規約：KST §5、Stacks 0815, Theorem 38.30.7、Noether 条件は中間環 A に課す。
使われ方：基礎環上有限でない加群の局所平坦化をさらに細分する。
-/
theorem finiteType_tensorPureTransform_flat_baseChange
    (R B A C M : Type*) [CommRing R] [CommRing B] [CommRing A] [CommRing C]
    [Algebra R B] [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [Algebra.FiniteType R B] [Module.Finite B M] [IsNoetherianRing A]
    (f : R) [Module.Flat A (modulePureTransform (algebraMap R A f) (A ⊗[R] M))]
    (hf : IsRegular (algebraMap R C f)) :
    Module.Flat C (modulePureTransform (algebraMap R C f) (C ⊗[R] M)) := by
  obtain ⟨n, hn⟩ := tensorAlgebraModule_boundaryTorsion_bounded R B A M (algebraMap R A f)
  have hf' : IsRegular (algebraMap A C (algebraMap R A f)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact hf
  have := flatPureTransform_baseChange_of_bound C (algebraMap R A f) (A ⊗[R] M) n hn hf'
  exact tensorPureTransform_flat_cancelBaseChange R A C M f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
