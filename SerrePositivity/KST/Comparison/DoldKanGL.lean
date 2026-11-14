module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Group.Submonoid.Basic
public import SerrePositivity.KST.Comparison.GammaRing
public import SerrePositivity.KST.Comparison.PiZeroRing
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Category.MonCat.Basic

/-!
# ĜL の入力となる単元成分の逆像

概要：KST §2.2、式 (2.2) の代数的な逆像を定義し、群とは限らないことを検証する。
方針：ℤ[X] の 1+X を零点と −1 で評価する。原典の群状単体的モノイドという区別を保つ。
規約：Γ の AW 環は GammaRing.lean、π₀ の環は PiZeroRing.lean に置く。
使われ方：正本 §13-10 の群状単体的モノイドと、単体的群との差を示す反例。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.KST.Comparison

universe u v

/--
概要：環準同型による単元の逆像を部分モノイドにする。
方針：単元の積に関する閉性を用いる。
規約：逆像の各元が元の環で可逆であるとは要求しない。
使われ方：KST §2.2、式 (2.2) の各単体次数での代数的構成。
-/
def unitsPreimage {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) : Submonoid R where
  carrier := {x | IsUnit (f x)}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change IsUnit (f (x * y))
    rw [map_mul]
    exact hx.mul hy

/--
概要：零点評価で整数の単元になる多項式の部分モノイド。
方針：`unitsPreimage` に評価準同型を適用する。
規約：これは単体的環そのものの構成ではなく、零次で現れる代数的模型である。
使われ方：KST 式 (2.2) と SS03 式 (2.9) の群とモノイドの区別を検証する。
-/
noncomputable def evalZeroUnits : Submonoid (Polynomial ℤ) :=
  unitsPreimage (Polynomial.evalRingHom (0 : ℤ))

/--
概要：1+X は零点評価による単元の逆像に属する。
方針：評価すると 1 になることを使う。
規約：多項式環での単元性は結論に含まない。
使われ方：KST 式 (2.2) の逆像が単元群と異なることの検証。
-/
theorem one_add_X_mem_evalZeroUnits :
    (1 + Polynomial.X : Polynomial ℤ) ∈ evalZeroUnits := by
  change IsUnit (Polynomial.evalRingHom (0 : ℤ) (1 + Polynomial.X))
  simp

/--
概要：整数係数多項式 1+X は単元ではない。
方針：右逆元との積を −1 で評価すると 0 = 1 となる。
規約：この評価による証明は原典にはない代数的な反例検証である。
使われ方：KST 式 (2.2) の逆像に群構造を要求できないことを示す。
-/
theorem not_isUnit_one_add_X : ¬ IsUnit (1 + Polynomial.X : Polynomial ℤ) := by
  intro h
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have h := congrArg (Polynomial.evalRingHom (-1 : ℤ)) hq
  simp at h

/--
概要：単元の逆像部分モノイドに属する 1+X は、その中に右逆元を持たない。
方針：部分モノイドの等式を多項式環に写し、−1 で評価する。
規約：部分モノイドの乗法を固定した主張であり、任意の別の群構造は扱わない。
使われ方：KST §2.2 の群状モノイドを単体的群と呼べないことの代数的根拠。
-/
theorem one_add_X_no_right_inverse :
    ¬ ∃ q : evalZeroUnits,
      (⟨1 + Polynomial.X, one_add_X_mem_evalZeroUnits⟩ : evalZeroUnits) * q = 1 := by
  rintro ⟨q, hq⟩
  have hp : (1 + Polynomial.X : Polynomial ℤ) * q.val = 1 :=
    congrArg (fun r : evalZeroUnits => r.val) hq
  have h := congrArg (Polynomial.evalRingHom (-1 : ℤ)) hp
  simp at h

end SerrePositivity.KST.Comparison

noncomputable section

namespace SerrePositivity.KST.Comparison

open CategoryTheory Opposite SSet
open scoped Simplicial

variable (A : SimplicialObject RingCat.{u}) (r : ℕ)

/--
概要：各次数の行列を π₀A 上の行列に送る環準同型。
方針：成分環への準同型を各行列成分に適用する。
規約：KST 式 (2.2) の右側の縦射。行列の rank は r、単体次数は q。
使われ方：ĜL_r(A) の各次数の定義。
-/
def matrixToComponents (q : ℕ) :
    Matrix (Fin r) (Fin r) (A.obj (op ⦋q⦌)) →+*
      Matrix (Fin r) (Fin r) (π₀ (ringSpace A)) :=
  (SimplicialRing.simplexToComponents A q).mapMatrix

/--
概要：行列の成分写像は面と退化で不変である。
方針：各行列成分に成分環への準同型の自然性を適用する。
規約：KST 式 (2.2) の単体的自然性。
使われ方：π₀ で可逆な行列の面・退化の閉性。
-/
theorem matrixToComponents_natural {p q : ℕ} (f : ⦋p⦌ ⟶ ⦋q⦌)
    (s : Matrix (Fin r) (Fin r) (A.obj (op ⦋q⦌))) :
    matrixToComponents A r p ((A.map f.op).hom.mapMatrix s) = matrixToComponents A r q s := by
  apply Matrix.ext
  intro i j
  exact SimplicialRing.simplexToComponents_natural A f (s i j)

/--
概要：π₀ で可逆な行列からなる各次数の部分モノイド。
方針：成分行列環の単元の逆像を取る。
規約：各次数で逆元を要求しない。KST 式 (2.2)、正本 §13-10。
使われ方：群状単体的モノイド ĜL_r(A) の台。
-/
def hatGLSubmonoid (q : ℕ) : Submonoid (Matrix (Fin r) (Fin r) (A.obj (op ⦋q⦌))) :=
  unitsPreimage (matrixToComponents A r q)

/--
概要：ĜL_r の面・退化をモノイド準同型として制限する。
方針：成分写像の自然性から単元の逆像の保存を得る。
規約：全ての単調写像に対する反変作用。KST 式 (2.2)。
使われ方：ĜL_r を単体的モノイドへまとめる。
-/
def hatGLPullback {p q : ℕ} (f : ⦋p⦌ ⟶ ⦋q⦌) :
    hatGLSubmonoid A r q →* hatGLSubmonoid A r p where
  toFun s := ⟨(A.map f.op).hom.mapMatrix s.val, by
    change IsUnit (matrixToComponents A r p ((A.map f.op).hom.mapMatrix s.val))
    rw [matrixToComponents_natural]
    exact s.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

/--
概要：π₀ で可逆な行列の群状単体的モノイドの単体的部分を構成する。
方針：各次数の部分モノイドと行列の面・退化をまとめる。
規約：KST 式 (2.2)。π₀ の群性の証明はこの定義には仮定しない。
使われ方：ΓA に適用する ĜL_r(A) と bar 構成。
-/
def hatGLMonoidObject : SimplicialObject MonCat.{u} where
  obj q := MonCat.of (hatGLSubmonoid A r q.unop.len)
  map f := MonCat.ofHom (hatGLPullback A r f.unop)
  map_id q := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro s
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change (A.map (𝟙 q)).hom (s.val i j) = s.val i j
    simp
  map_comp f g := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro s
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change (A.map (f ≫ g)).hom (s.val i j) =
      (A.map g).hom ((A.map f).hom (s.val i j))
    simp

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (2.2)" (partial := component) "仮定：単位つき単体環の有限階数行列を用いる（Lean が強い：原典は非単位的環も含む）。結論：指定成分に制限した行列モノイドとその成分群。任意の非単位的単体環の安定化した ĜL までの同定は別（Lean が弱い）。"] _root_.SerrePositivity.KST.Comparison.hatGLMonoidObject
