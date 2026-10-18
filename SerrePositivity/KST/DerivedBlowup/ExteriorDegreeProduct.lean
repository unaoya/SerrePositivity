module

public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeMap

/-!
概要：KST Def3.1 の Koszul 外積模型の同次積と単位を線形写像として構成する。
方針：総外積代数の積を第n外積と第m外積へ制限する。
規約：同次積の値域の次数を等式で明示する。
使われ方：整数 cochain 複体の tensor 積からの乗法射。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R] {M N : Type v}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 概要：第n外積と第m外積の同次積。
方針：総外積の積を双線形写像として部分加群へ制限する。
規約：KST Def3.1、値域次数kには n+m=k を要求。
使われ方：各双次数での Koszul 複体の乗法成分。 -/
def exteriorDegreeProduct (n m k : ℕ) (h : n + m = k) :
    ExteriorAlgebra.exteriorPower R n M →ₗ[R]
      ExteriorAlgebra.exteriorPower R m M →ₗ[R] ExteriorAlgebra.exteriorPower R k M where
  toFun x :=
    { toFun := fun y => ⟨x.val * y.val, by simpa only [← h] using
        (SetLike.mul_mem_graded x.property y.property)⟩
      map_add' := fun y z => Subtype.ext (mul_add x.val y.val z.val)
      map_smul' := fun r y => Subtype.ext (mul_smul_comm r x.val y.val) }
  map_add' x z := by
    ext y
    exact add_mul x.val z.val y.val
  map_smul' r x := by
    ext y
    exact smul_mul_assoc r x.val y.val

/-- 概要：同次積を総外積に含めると通常の積になる。
方針：構成の定義を展開する。規約：KST Def3.1。
使われ方：Leibniz 則と結合則を総外積代数で確認する。 -/
@[simp] theorem exteriorDegreeProduct_val (n m k : ℕ) (h : n + m = k)
    (x : ExteriorAlgebra.exteriorPower R n M) (y : ExteriorAlgebra.exteriorPower R m M) :
    (exteriorDegreeProduct n m k h x y).val = x.val * y.val := rfl

/-- 概要：基底環の係数を第0外積に含める線形単位射。
方針：algebraMap の像が部分加群の0乗に属することを使う。
規約：KST Def3.1。使われ方：Koszul dg 代数の単位。 -/
def exteriorDegreeUnit : R →ₗ[R] ExteriorAlgebra.exteriorPower R 0 M :=
  (Algebra.linearMap R (ExteriorAlgebra R M)).codRestrict _ Submodule.algebraMap_mem

/-- 概要：基底変換の各外積写像は同次積を保つ。
方針：部分加群への包含で比較し、総外積の環射の乗法保存を用いる。
規約：KST §3.1。使われ方：Koszul チャート遷移の dg 代数としての乗法保存。 -/
theorem exteriorDegreeMap_product (f : M →ₗ[R] N) (n m k : ℕ) (h : n + m = k)
    (x : ExteriorAlgebra.exteriorPower R n M) (y : ExteriorAlgebra.exteriorPower R m M) :
    exteriorDegreeMap f k (exteriorDegreeProduct n m k h x y) =
      exteriorDegreeProduct n m k h (exteriorDegreeMap f n x) (exteriorDegreeMap f m y) := by
  apply Subtype.ext
  exact map_mul (ExteriorAlgebra.map f) x.val y.val

end SerrePositivity.KST.DerivedBlowup
