module

public import SerrePositivity.EInfinity.BarrattEccles.NormalizedNaturality
public import SerrePositivity.EInfinity.BarrattEccles.NormalizedDegreeTransport

/-!
# arity と鎖次数の等式による移送

概要：Berger–Fresse §1.1.3 の左単位則で現れる arity と次数の等式を扱う。
方針：arity の等式を単体集合の射へ送り、鎖次数の等式を単体圏の射へ送る。
規約：有限集合の同定は順序と自然数としての値を保つ。
使われ方：arity 0+n と鎖次数 0+q の計算を既存の単位子へ接続する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：arity の等式が定める単体集合の射（Berger–Fresse §1.1.3）。
方針：arity 成分へ等式を適用して等式の射を取る。
規約：新たな同値の選択を含まない。
使われ方：左単位則の出力 arity を移送する。 -/
def simplicialArityMap {m n : ℕ} (h : m = n) : simplicial m ⟶ simplicial n :=
  eqToHom (congrArg simplicial h)

/-- 概要：arity の等式による射は各頂点の置換を有限集合の同値で共役する（Berger–Fresse §0.10）。
方針：等式を消去して恒等写像の場合へ帰着する。
規約：頂点番号は変えない。
使われ方：左単位則を置換の単位則で計算する。 -/
lemma simplexEquiv_arityMap {m n : ℕ} (h : m = n) (q : ℕ)
    (x : (simplicial m) _⦋q⦌) (j : Fin (q + 1)) :
    simplexEquiv n q ((simplicialArityMap h).app _ x) j =
      (finCongr h).permCongr (simplexEquiv m q x j) := by
  cases h
  rfl

/-- 概要：鎖次数の等式が定める単体圏の射（Berger–Fresse §1.1.3）。
方針：有限頂点の次数を Fin.cast で移し、同じ順序を保つ。
規約：向きは [r] から [t] である。
使われ方：次数0の入力との shuffle の出力を元の単体と比較する。 -/
def degreeCastMap {r t : ℕ} (h : r = t) : ⦋r⦌ ⟶ ⦋t⦌ :=
  SimplexCategory.mkHom {
    toFun k := Fin.cast (congrArg (fun d => d + 1) h) k
    monotone' := fun _ _ h => h }

variable (A : Type u) [CommRing A]

/-- 概要：正規化鎖は arity の等式の射をそのまま移送する（Berger–Fresse §1.1.2）。
方針：arity の等式を消去して関手の恒等射の保存を使う。
規約：複体の射としての等式である。
使われ方：arity の移送をオペラッドの単位則の文言へ合わせる。 -/
lemma normalizedChainMap_arityMap {m n : ℕ} (h : m = n) :
    normalizedChainMap A (simplicialArityMap h) = eqToHom (congrArg (normalizedChains A) h) := by
  cases h
  simp only [simplicialArityMap, eqToHom_refl, normalizedChainMap, CategoryTheory.Functor.map_id]

/-- 概要：整数コチェインの正規化関手は arity の等式の射を保存する（Berger–Fresse §1.1.2）。
方針：arity の等式を消去して関手の恒等射の保存を使う。
規約：出力は整数次数の複体の等式の射である。
使われ方：左単位則の arity の移送を単体集合の射で計算する。 -/
lemma normalizedFunctor_arityMap {m n : ℕ} (h : m = n) :
    (normalizedFunctor A).map (simplicialArityMap h) = eqToHom (congrArg (complex A) h) := by
  cases h
  simp only [simplicialArityMap, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- 概要：次数の等式の引き戻しと正規化生成元の移送は互いに打ち消す（Berger–Fresse §1.1.2）。
方針：等式を消去し、単体圏の恒等射の引き戻しを簡約する。
規約：単体の次数は t、引き戻した生成元の次数は r である。
使われ方：左単位則の shuffle 和の出力次数を元へ戻す。 -/
lemma degreeTransport_generator_degreeCast (n : ℕ) {r t : ℕ} (h : r = t)
    (x : (simplicial n) _⦋t⦌) :
    degreeTransport A n h (normalizedGenerator A n r ((simplicial n).map (degreeCastMap h).op x)) =
      normalizedGenerator A n t x := by
  cases h
  rw [degreeTransport_refl]
  change normalizedGenerator A n r ((simplicial n).map (𝟙 (Opposite.op ⦋r⦌)) x) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- 概要：正規化鎖の射は次数の等式による移送と可換する（Berger–Fresse §1.1.2）。
方針：次数の等式を消去する。
規約：arity の異なる二つの正規化鎖の射も扱う。
使われ方：左単位則で arity の移送と鎖次数の移送の順を交換する。 -/
lemma degreeTransport_naturality {m n r t : ℕ} (f : normalizedChains A m ⟶ normalizedChains A n)
    (h : r = t) (z : (normalizedChains A m).X r) :
    f.f t (degreeTransport A m h z) = degreeTransport A n h (f.f r z) := by
  cases h
  rfl

end SerrePositivity.EInfinity.BarrattEccles
