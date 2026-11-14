module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.Data.Quot
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexComponents
public import Mathlib.Tactic.Abel

/-!
# 単体的環の連結成分の環

概要：Mathlib の連結成分 π₀ に単体的環の演算を降ろす。
方針：辺の和と積、逆元の辺を構成し、商に演算と環の法則を降ろす。
規約：π₀ 自体の定義は Mathlib のものを用いる。高次 π_n は定義しない。
使われ方：KST §2.2、式 (2.2) の GL_n(π₀A) と群状性。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：単体的環の台単体集合。
方針：環から型への忘却関手を合成する。
規約：KST §2.2 の π₀ はこの単体集合の連結成分。
使われ方：辺の演算と Γ の環の連結成分。
-/
abbrev ringSpace (A : SimplicialObject RingCat.{u}) : SSet.{u} := A ⋙ forget RingCat

namespace SimplicialRing

variable (A : SimplicialObject RingCat.{u})

local instance (n : SimplexCategoryᵒᵖ) : Ring ((ringSpace A).obj n) :=
  inferInstanceAs (Ring (A.obj n))

/--
概要：単体的環の二本の辺を足す。
方針：一次単体を足し、環準同型である二つの面写像を適用する。
規約：始点・終点をそれぞれ足す。KST §2.2 の加法的 π₀ の構成。
使われ方：π₀ の加法の代表独立性。
-/
def edgeAdd {a b c d : A.obj (op ⦋0⦌)} (e : (ringSpace A).Edge a b)
    (f : (ringSpace A).Edge c d) : (ringSpace A).Edge (a + c) (b + d) :=
  .mk (e.edge + f.edge)
    (by change (A.map (SimplexCategory.δ 1).op).hom (e.edge + f.edge) = _
        rw [map_add]; exact congrArg₂ (· + ·) e.src_eq f.src_eq)
    (by change (A.map (SimplexCategory.δ 0).op).hom (e.edge + f.edge) = _
        rw [map_add]; exact congrArg₂ (· + ·) e.tgt_eq f.tgt_eq)

/--
概要：単体的環の二本の辺を掛ける。
方針：一次単体の積の両面を環準同型性で計算する。
規約：非可換の順序を保つ。KST 式 (2.2) の乗法的 π₀。
使われ方：π₀ の積の代表独立性。
-/
def edgeMul {a b c d : A.obj (op ⦋0⦌)} (e : (ringSpace A).Edge a b)
    (f : (ringSpace A).Edge c d) : (ringSpace A).Edge (a * c) (b * d) :=
  .mk (e.edge * f.edge)
    (by change (A.map (SimplexCategory.δ 1).op).hom (e.edge * f.edge) = _
        rw [map_mul]; exact congrArg₂ (· * ·) e.src_eq f.src_eq)
    (by change (A.map (SimplexCategory.δ 0).op).hom (e.edge * f.edge) = _
        rw [map_mul]; exact congrArg₂ (· * ·) e.tgt_eq f.tgt_eq)

/--
概要：単体的環の辺の加法的逆を取る。
方針：一次単体の負元を両面で評価する。
規約：KST §2.2 の加法群の演算。
使われ方：π₀ の負元の代表独立性。
-/
def edgeNeg {a b : A.obj (op ⦋0⦌)} (e : (ringSpace A).Edge a b) :
    (ringSpace A).Edge (-a) (-b) :=
  .mk (-e.edge)
    (by change (A.map (SimplexCategory.δ 1).op).hom (-e.edge) = _
        rw [map_neg]; exact congrArg Neg.neg e.src_eq)
    (by change (A.map (SimplexCategory.δ 0).op).hom (-e.edge) = _
        rw [map_neg]; exact congrArg Neg.neg e.tgt_eq)

/--
概要：単体的環では任意の辺を逆向きの辺に置き換えられる。
方針：a+b の定数辺から与えられた辺を引く。
規約：環の加法群だけを使う。KST §2.2 の π₀ の計算。
使われ方：連結成分の等式を一本の辺で表す。
-/
def edgeReverse {a b : A.obj (op ⦋0⦌)} (e : (ringSpace A).Edge a b) :
    (ringSpace A).Edge b a :=
  (edgeAdd A (.id (a + b)) (edgeNeg A e)).ofEq (by abel) (by abel)

/--
概要：単体的環の二本の連続する辺を一本にまとめる。
方針：二本の辺を足して中間点の定数辺を引く。
規約：Kan 充填を仮定しない。KST §2.2 の加法的な成分計算。
使われ方：行列の各成分の辺を一つの行列の辺にまとめる。
-/
def edgeConcat {a b c : A.obj (op ⦋0⦌)}
    (e : (ringSpace A).Edge a b) (f : (ringSpace A).Edge b c) :
    (ringSpace A).Edge a c :=
  (edgeAdd A (edgeAdd A e f) (.id (-b))).ofEq (by abel) (by abel)

/--
概要：単体的環の同じ成分にある二頂点は一本の辺で結べる。
方針：辺関係の同値閉包に帰納し、加法による逆向きと連結を使う。
規約：π₀ 自体は Mathlib のもの。KST 式 (2.2) の比較。
使われ方：π₀ と有限行列の可換性、ĜL の π₀ の単射性。
-/
theorem nonempty_edge_of_mk_eq {a b : A.obj (op ⦋0⦌)}
    (h : (π₀.mk a : π₀ (ringSpace A)) = π₀.mk b) : Nonempty ((ringSpace A).Edge a b) := by
  have hr := (π₀.mk_eq_mk_iff (X := ringSpace A) a b).mp h
  clear h
  induction hr with
  | rel a b h => exact h
  | refl a => exact ⟨Edge.id (X := ringSpace A) a⟩
  | symm a b h ih => exact ih.map (edgeReverse A)
  | trans a b c h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e⟩ := ih₁
    obtain ⟨f⟩ := ih₂
    exact ⟨edgeConcat A e f⟩

unseal SSet.π₀ in
/--
概要：π₀ の二つの成分を足す。
方針：辺の和で二重商への写像の適切性を証明する。
規約：π₀ の型を変更しない。KST §2.2 の環構造。
使われ方：連結成分の環。
-/
def componentsAdd : π₀ (ringSpace A) → π₀ (ringSpace A) → π₀ (ringSpace A) :=
  Quot.lift₂ (fun a b => π₀.mk (a + b))
    (by rintro a b c ⟨e⟩; exact π₀.sound (edgeAdd A (.id a) e))
    (by rintro a b c ⟨e⟩; exact π₀.sound (edgeAdd A e (.id c)))

unseal SSet.π₀ in
/--
概要：π₀ の二つの成分を掛ける。
方針：辺の積で二重商への写像を定義する。
規約：非可換積の順序は元の環と同じ。KST 式 (2.2)。
使われ方：GL_n(π₀A) の係数環。
-/
def componentsMul : π₀ (ringSpace A) → π₀ (ringSpace A) → π₀ (ringSpace A) :=
  Quot.lift₂ (fun a b => π₀.mk (a * b))
    (by rintro a b c ⟨e⟩; exact π₀.sound (edgeMul A (.id a) e))
    (by rintro a b c ⟨e⟩; exact π₀.sound (edgeMul A e (.id c)))

/--
概要：連結成分の加法の型クラス。
方針：商に降ろした演算の定義を使う。
規約：KST §2.2、π₀A の環構造。
使われ方：成分環への標準準同型と ĜL の構成。
-/
instance componentsAddInst : Add (π₀ (ringSpace A)) := ⟨componentsAdd A⟩
/--
概要：連結成分の乗法の型クラス。
方針：商に降ろした演算の定義を使う。
規約：KST §2.2、π₀A の環構造。
使われ方：成分環への標準準同型と ĜL の構成。
-/
instance componentsMulInst : Mul (π₀ (ringSpace A)) := ⟨componentsMul A⟩
/--
概要：零単体の零の連結成分。
方針：商に降ろした演算の定義を使う。
規約：KST §2.2、π₀A の環構造。
使われ方：成分環への標準準同型と ĜL の構成。
-/
instance componentsZeroInst : Zero (π₀ (ringSpace A)) := ⟨π₀.mk 0⟩
/--
概要：零単体の単位元の連結成分。
方針：商に降ろした演算の定義を使う。
規約：KST §2.2、π₀A の環構造。
使われ方：成分環への標準準同型と ĜL の構成。
-/
instance componentsOneInst : One (π₀ (ringSpace A)) := ⟨π₀.mk 1⟩
/--
概要：連結成分の負元の型クラス。
方針：商に降ろした演算の定義を使う。
規約：KST §2.2、π₀A の環構造。
使われ方：成分環への標準準同型と ĜL の構成。
-/
instance componentsNegInst : Neg (π₀ (ringSpace A)) :=
  ⟨π₀.lift (fun a => π₀.mk (-a)) (fun _ _ e => π₀.sound (edgeNeg A e))⟩

/--
概要：連結成分の商写像は加法を保つ。
方針：商に降ろした演算の定義を使う。
規約：KST §2.2、π₀A の環構造。
使われ方：成分環への標準準同型と ĜL の構成。
-/
@[simp] theorem mk_add (a b : A.obj (op ⦋0⦌)) :
    (π₀.mk (a + b) : π₀ (ringSpace A)) = π₀.mk a + π₀.mk b := rfl
/--
概要：連結成分の商写像は乗法を保つ。
方針：商に降ろした演算の定義を使う。
規約：KST §2.2、π₀A の環構造。
使われ方：成分環への標準準同型と ĜL の構成。
-/
@[simp] theorem mk_mul (a b : A.obj (op ⦋0⦌)) :
    (π₀.mk (a * b) : π₀ (ringSpace A)) = π₀.mk a * π₀.mk b := rfl
/--
概要：連結成分の商写像は負元を保つ。
方針：商に降ろした演算の定義を使う。
規約：KST §2.2、π₀A の環構造。
使われ方：成分環への標準準同型と ĜL の構成。
-/
@[simp] theorem mk_neg (a : A.obj (op ⦋0⦌)) :
    (π₀.mk (-a) : π₀ (ringSpace A)) = -π₀.mk a := rfl

/--
概要：単体的環の連結成分に環構造を与える。
方針：各法則を零次単体の代表へ帰着し、元の環の法則を商へ送る。
規約：高次の Kan 性は不要。KST §2.2 の π₀A の環。
使われ方：群状単体的モノイド ĜL_n の定義。
-/
instance componentsRing : Ring (π₀ (ringSpace A)) where
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    induction c using π₀.rec with | mk c => ?_
    exact congrArg π₀.mk (add_assoc a b c)
  zero_add a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (zero_add a)
  add_zero a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (add_zero a)
  add_comm a b := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => exact congrArg π₀.mk (add_comm a b)
  neg_add_cancel a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (neg_add_cancel a)
  mul_assoc a b c := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    induction c using π₀.rec with | mk c => ?_
    exact congrArg π₀.mk (mul_assoc a b c)
  one_mul a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (one_mul a)
  mul_one a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (mul_one a)
  zero_mul a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (zero_mul a)
  mul_zero a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (mul_zero a)
  left_distrib a b c := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    induction c using π₀.rec with | mk c => ?_
    exact congrArg π₀.mk (mul_add a b c)
  right_distrib a b c := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    induction c using π₀.rec with | mk c => ?_
    exact congrArg π₀.mk (add_mul a b c)

/--
概要：零次単体から連結成分への環準同型。
方針：商への標準射と演算の定義を使う。
規約：全射性は Mathlib の π₀.mk_surjective。KST 式 (2.2) の次数零の縦射。
使われ方：π₀ で可逆な行列を取り出す。
-/
def toComponents : A.obj (op ⦋0⦌) →+* π₀ (ringSpace A) where
  toFun := fun a => (π₀.mk a : π₀ (ringSpace A))
  map_zero' := rfl
  map_one' := rfl
  map_add' := mk_add A
  map_mul' := mk_mul A

/--
概要：各次数の単体から π₀ への成分写像を環準同型として与える。
方針：最初の頂点への環準同型の後に零次の商写像を合成する。
規約：頂点による差は成分では消える。KST 式 (2.2) の縦写像。
使われ方：行列環に適用して可逆な成分の逆像を取る。
-/
def simplexToComponents (n : ℕ) : A.obj (op ⦋n⦌) →+* π₀ (ringSpace A) :=
  (toComponents A).comp (A.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op).hom

/--
概要：成分への環準同型は全ての単体作用と可換である。
方針：`simplexClass_map` を環の台の単体集合に適用する。
規約：KST 式 (2.2) の縦写像の単体的自然性。
使われ方：ĜL_n の面・退化が単元の逆像を保つこと。
-/
theorem simplexToComponents_natural {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (s : A.obj (op ⦋n⦌)) :
    simplexToComponents A m ((A.map f.op).hom s) = simplexToComponents A n s :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_map (ringSpace A) f s

end SimplicialRing

end SerrePositivity.KST.Comparison
