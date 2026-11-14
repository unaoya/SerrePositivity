module
public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.HomologicalAlgebra.DerivedTensor
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Algebra.Defs

public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-!
# 恒等写像の完全忠実平坦性

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v

/-! ## AlgebraColimit（旧 Andre/Transfinite/AlgebraColimit.lean） -/

@[expose] public noncomputable section Existence

open SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
/-- ## 概要
任意の可換環 R は、自身上で任意のイデアル I に関して完全忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復。

## 方針
R の平坦性から正次数 Tor を消し、剰余テンソルを剰余環自身と線形同型で比較する。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
theorem isCompletelyFaithfullyFlat_self (I : Ideal R) : IsCompletelyFaithfullyFlat I R := by
  constructor
  · intro N _ _ hN
    apply (isConcentratedInDegreeZero_derivedTensor_iff R N).mpr
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact torModule_subsingleton_of_flat R N m
  · exact Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) (R ⧸ I)
      (TensorProduct.AlgebraTensorModule.rid R (R ⧸ I) (R ⧸ I))

end SerrePositivity.BhattScholze.Andre.Transfinite

end Existence

/-! ## SingleRoot（旧 Andre/Transfinite/SingleRoot.lean） -/

