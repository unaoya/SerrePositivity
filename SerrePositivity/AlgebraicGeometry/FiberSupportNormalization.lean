module

public import SerrePositivity.AlgebraicGeometry.FiberSupportAnnihilator
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
概要：有限加群のファイバーの台の次元を、零化イデアルで切り出した閉部分スキームのファイバー次元として表す。
方針：基底変換後の台を零点集合で表し、商とテンソル積の比較を使う。
規約：元の有限加群を定める零化イデアルを用いる。
使われ方：Stacks 057S の相対正規化を有限加群の台に適用する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：底変換後の有限加群の台の次元は、元の零化イデアルによる商の底変換の Krull 次元に等しい。
方針：底変換後の台の零点集合を商環のスペクトルにし、商の底変換を比較する。
規約：底変換環は体に限定しない。
使われ方：次元帰納でのファイバーの台の上限を、閉部分スキームの相対正規化に渡す。
-/
theorem supportDim_baseChange_eq_ringKrullDim_quotientAnnihilator
    {R B K M : Type*} [CommRing R] [CommRing B] [CommRing K] [Algebra R B] [Algebra R K]
    [AddCommGroup M] [Module B M] [Module.Finite B M] :
    Module.supportDim (B ⊗[R] K) ((B ⊗[R] K) ⊗[B] M) =
      ringKrullDim (K ⊗[R] (B ⧸ Module.annihilator B M)) := by
  let D := B ⊗[R] K
  let I := Module.annihilator B M
  let E := B ⧸ I
  let e₀ := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot D I).toRingEquiv
  let e₁ := (Algebra.TensorProduct.comm B D E).toRingEquiv
  let e₂ := (Algebra.TensorProduct.cancelBaseChange R B E E K).toRingEquiv
  let e₃ := (Algebra.TensorProduct.comm R E K).toRingEquiv
  rw [Module.supportDim, support_tensorProduct_eq_zeroLocus_map_annihilator,
    ← ringKrullDim_quotient]
  exact ringKrullDim_eq_of_ringEquiv (e₀.trans (e₁.trans (e₂.trans e₃)))

end SerrePositivity.AlgebraicGeometry
