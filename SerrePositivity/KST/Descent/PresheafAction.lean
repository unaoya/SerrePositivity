module

public import SerrePositivity.KST.Descent.Axioms
public import SerrePositivity.KST.Descent.InvariantExactness

/-!
# 反変前層の群作用と指定された降下比較

## 概要
スキームの自己同型の左作用から前層の各次数への左作用を作り、
既存の固定部分の定義を有理表現の不変部分と一致させる。

## 方針
`g` の作用を `g⁻¹` による引き戻しとする。
引き戻しの反変性と自己同型の積の順序の双方を明示して群の法則を確認する。

## 規約
既存の K₀ の `g • [P] = [twist g⁻¹ P]` と同じ向き。
通常の不変部分とホモトピー固定点の比較はここでは主張しない。

## 使われ方
論文 (3.7) の指定比較に有理不変部分の完全性を適用し、(3.8) と軌道正方形を扱う。
-/

@[expose] public section

universe u v w t

open CategoryTheory Opposite Representation

namespace SerrePositivity.KST.Descent.GradedPresheaf

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient)

/-- 概要：逆元の引き戻しによる各次数の左表現（論文 (3.7)）。
方針：反変合成と自己同型の積を使い、群の乗法との両立を証明する。
規約：`g` の作用は `(g⁻¹)*`。係数 H は基底から引かれるものとして固定する。
使われ方：幾何学的な群作用に不変部分の完全性を適用する。 -/
def pullbackRepresentation (H : Coefficient) (n : ℤ) {X : C} {G : Type*} [Group G]
    (action : G →* Aut X) : Representation ℚ G ((L H n).obj (op X)) where
  toFun g := L.pullback H n (action g⁻¹).asIso.hom
  map_one' := by
    simp only [inv_one, map_one, Aut.one_asIso, Iso.refl_hom, pullback_id]
    rfl
  map_mul' g h := by
    simp only [mul_inv_rev, map_mul, Aut.mul_asIso, Iso.trans_hom, pullback_comp]
    rfl

/-- 概要：自己同型による固定条件は逆元の左表現の不変部分と一致（論文 (3.7)–(3.8)）。
方針：全群元を逆元で取り直す。
規約：この一致には有限性や平均作用素は不要。
使われ方：`invariantComparison` の値域を既存の表現の API に接続する。 -/
theorem invariantSubmodule_eq_representationInvariants (H : Coefficient) (n : ℤ)
    {X : C} {G : Type*} [Group G] (action : G →* Aut X) :
    L.invariantSubmodule H n action = (L.pullbackRepresentation H n action).invariants := by
  ext x
  change (∀ g, L.pullback H n (action g).asIso.hom x = x) ↔
    ∀ g, L.pullback H n (action g⁻¹).asIso.hom x = x
  constructor
  · intro h g
    exact h g⁻¹
  · intro h g
    simpa only [inv_inv] using h g⁻¹

/-- 概要：固定部分の二つの記述の恒等的な線形同型（論文 (3.7)）。
方針：固定条件の一致を使い、値を変えずに部分型を移す。
規約：作用の向きを変えるための無関係な抽象同型ではない。
使われ方：指定した降下比較の値を表現の不変部分へ移す。 -/
noncomputable def invariantSubmoduleEquiv (H : Coefficient) (n : ℤ)
    {X : C} {G : Type*} [Group G] (action : G →* Aut X) :
    L.invariantSubmodule H n action ≃ₗ[ℚ] (L.pullbackRepresentation H n action).invariants where
  toFun x := ⟨x.val, by
    rw [← L.invariantSubmodule_eq_representationInvariants H n action]
    exact x.property⟩
  invFun x := ⟨x.val, by
    rw [L.invariantSubmodule_eq_representationInvariants H n action]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：基底からの引き戻しは自明表現からの同変線形写像（論文 (3.7)）。
方針：基底上の自己同型の引き戻しが引き戻した類を固定することを使う。
規約：基底では自明作用、上では逆元による左作用。
使われ方：降下の指定写像を不変部分の完全関手の入力とする。 -/
def equivariantPullback (H : Coefficient) (n : ℤ) {X Y : C} (f : X ⟶ Y)
    {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) :
    IntertwiningMap (Representation.trivial ℚ G ((L H n).obj (op Y)))
      (L.pullbackRepresentation H n action) where
  toLinearMap := L.pullback H n f
  isIntertwining' g := by
    ext x
    change L.pullback H n f x =
      L.pullback H n (action g⁻¹).asIso.hom (L.pullback H n f x)
    exact (L.pullback_mem_invariantSubmodule H n f action over_base x g⁻¹).symm

/-- 概要：不変部分への表現論的な制限は元の降下比較と一致（論文 (3.7)）。
方針：両辺の値が同じ幾何学的な引き戻しであることを確認する。
規約：単なる同型の存在ではなく、指定写像の可換性を示す。
使われ方：有理不変部分の完全性を `PiDescent` の証明に接続する。 -/
theorem invariantMap_equivariantPullback (H : Coefficient) (n : ℤ) {X Y : C}
    (f : X ⟶ Y) {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) (x : (L H n).obj (op Y)) :
    invariantMap (L.equivariantPullback H n f action over_base)
        ((trivialInvariantsEquiv (Representation.trivial ℚ G ((L H n).obj (op Y)))).symm x) =
      L.invariantSubmoduleEquiv H n action (L.invariantComparison H n f action over_base x) :=
  rfl

end SerrePositivity.KST.Descent.GradedPresheaf
