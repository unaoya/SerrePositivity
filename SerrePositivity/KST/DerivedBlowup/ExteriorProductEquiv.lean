module

public import SerrePositivity.KST.DerivedBlowup.ExteriorProductSplit

/-!
概要：KST Def3.1 の生成元追加で総外積を二成分に分解する線形同型。
方針：第一成分は最後の座標での収縮後の射影、第二成分は単なる射影。
規約：復元は in(y)+e_last in(x)。cone の shifted 成分を先に置く。
使われ方：反復 cone の直和項との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：追加した生成元を除いて残る外積成分。
方針：最後の座標で収縮し、第一因子へ射影する。
規約：KST Def3.1。使われ方：cone の shifted 成分。 -/
def exteriorProductTail : ExteriorAlgebra R (M × R) →ₗ[R] ExteriorAlgebra R M :=
  exteriorProductOut.toLinearMap.comp (CliffordAlgebra.contractLeft (Q := 0) (LinearMap.snd R M R))

/-- 概要：二つの外積成分から生成元追加後の外積を復元する。
方針：第二成分を埋め込み、第一成分に最後の生成元を左から外積する。
規約：KST Def3.1。使われ方：二成分同型の逆写像。 -/
def exteriorProductJoin :
    (ExteriorAlgebra R M × ExteriorAlgebra R M) →ₗ[R] ExteriorAlgebra R (M × R) where
  toFun z := exteriorProductIn z.2 + exteriorProductLast * exteriorProductIn z.1
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]; abel
  map_smul' r z := by simp

/-- 概要：復元した外積の射影は第二成分。
方針：最後の生成元が射影で零になることを使う。
規約：KST Def3.1。使われ方：二成分同型の右逆。 -/
@[simp] theorem exteriorProductOut_join (x y : ExteriorAlgebra R M) :
    exteriorProductOut (exteriorProductJoin (x, y)) = y := by
  simp [exteriorProductJoin, exteriorProductOut, exteriorProductLast,
    ExteriorAlgebra.map_apply_ι]

/-- 概要：復元した外積の収縮成分は第一成分。
方針：最後の座標は最後の生成元で1、第一因子上で0である。
規約：KST Def3.1。使われ方：二成分同型の右逆。 -/
@[simp] theorem exteriorProductTail_join (x y : ExteriorAlgebra R M) :
    exteriorProductTail (exteriorProductJoin (x, y)) = x := by
  simp [exteriorProductTail, exteriorProductJoin, exteriorProductLast,
    CliffordAlgebra.contractLeft_ι_mul]

/-- 概要：追加生成元での分解と復元は線形同型。
方針：総外積の分解公式と二つの成分回収公式を使う。
規約：KST Def3.1、第一成分が shifted 成分。
使われ方：反復 cone 比較の次数別同型の基礎。 -/
def exteriorProductLinearEquiv : ExteriorAlgebra R (M × R) ≃ₗ[R]
    (ExteriorAlgebra R M × ExteriorAlgebra R M) :=
  LinearEquiv.ofLinearMap (exteriorProductTail.prod exteriorProductOut.toLinearMap)
    exteriorProductJoin (by
      apply LinearMap.ext
      intro z
      apply Prod.ext
      · exact exteriorProductTail_join z.1 z.2
      · exact exteriorProductOut_join z.1 z.2) (by
      apply LinearMap.ext
      intro z
      exact (exteriorProduct_decomposition z).symm)

end SerrePositivity.KST.DerivedBlowup
