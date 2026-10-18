module

public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeZero

/-!
概要：KST Def3.1 の Koszul 同次包含と標準同型・添字変更の整合性。
方針：標準同型の逆元律を評価し、添字の等式は等式帰納法で扱う。
規約：整数次数と自然数の外積次数の比較をここに集約する。
使われ方：生成元追加の二成分分解を cochain の各項へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：負次数の標準同型の逆と総外積への包含の合成。
方針：同型の逆元律を部分加群の値で評価する。
規約：KST Def3.1。使われ方：次数別外積分解の整数次数への移送。 -/
@[simp] theorem exteriorCochainInclusion_standard_inv (d : M →ₗ[R] R) (n : ℕ)
    (z : ExteriorAlgebra.exteriorPower R n M) :
    exteriorCochainInclusion d (-(n : ℤ)) ((exteriorKoszulCochainXIso d n).inv z) = z.val := by
  rw [exteriorCochainInclusion_neg]
  change ((exteriorKoszulCochainXIso d n).hom.hom
    ((exteriorKoszulCochainXIso d n).inv.hom z)).val = z.val
  exact congrArg Subtype.val (congr($((exteriorKoszulCochainXIso d n).inv_hom_id).hom z))

/-- 概要：添字の等式による同型は総外積への包含を変えない。
方針：添字の等式を消去する。
規約：KST Def3.1。使われ方：q+1=−n の次数変換。 -/
@[simp] theorem exteriorCochainInclusion_XIsoOfEq (d : M →ₗ[R] R)
    {p q : ℤ} (h : p = q) (z : (exteriorKoszulCochain d).X p) :
    exteriorCochainInclusion d q ((exteriorKoszulCochain d).XIsoOfEq h |>.hom <| z) =
      exteriorCochainInclusion d p z := by
  subst q
  rfl

/-- 概要：添字等式による逆同型も総外積への包含を変えない。
方針：添字の等式を消去する。
規約：KST Def3.1。使われ方：標準同型の逆からの移送。 -/
@[simp] theorem exteriorCochainInclusion_XIsoOfEq_inv (d : M →ₗ[R] R)
    {p q : ℤ} (h : p = q) (z : (exteriorKoszulCochain d).X q) :
    exteriorCochainInclusion d p ((exteriorKoszulCochain d).XIsoOfEq h |>.inv <| z) =
      exteriorCochainInclusion d q z := by
  subst q
  rfl

/-- 概要：次数0の基底環同型の逆は係数の包含になる。
方針：単位射の次数0成分との比較を使う。
規約：KST Def3.1。使われ方：二成分分解の次数0での比較。 -/
@[simp] theorem exteriorCochainInclusion_zero_inv (d : M →ₗ[R] R) (r : R) :
    exteriorCochainInclusion d 0 ((exteriorCochainZeroIso d).inv r) =
      algebraMap R (ExteriorAlgebra R M) r := by
  rw [← exteriorKoszulUnit_f_zero]
  exact exteriorKoszulUnit_inclusion d r

/-- 概要：任意の次数0の元は基底環同型の値を係数として包含される。
方針：次数0同型の往復を使う。
規約：KST Def3.1。使われ方：生成元追加の射影と次数0比較。 -/
theorem exteriorCochainInclusion_zero (d : M →ₗ[R] R) (z : (exteriorKoszulCochain d).X 0) :
    exteriorCochainInclusion d 0 z =
      algebraMap R (ExteriorAlgebra R M) ((exteriorCochainZeroIso d).hom z) := by
  have hi := congr($((exteriorCochainZeroIso d).hom_inv_id).hom z)
  change (exteriorCochainZeroIso d).inv ((exteriorCochainZeroIso d).hom z) = z at hi
  rw [← exteriorCochainInclusion_zero_inv d ((exteriorCochainZeroIso d).hom z), hi]

end SerrePositivity.KST.DerivedBlowup
