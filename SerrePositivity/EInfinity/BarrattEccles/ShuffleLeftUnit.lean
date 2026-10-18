module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleRightUnit
public import SerrePositivity.EInfinity.BarrattEccles.ArityDegreeTransport

/-!
# shuffle 部分合成の左単位の計算

概要：Berger–Fresse §1.1.3 の単位単体への代入を arity と次数の移送を含めて計算する。
方針：水平次数0の経路を一項にし、各頂点の置換の左単位則を使う。
規約：出力 arity 0+n と鎖次数 0+q は、それぞれ n と q へ移送する。
使われ方：部分合成の複体の射の左単位則を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：単位単体への shuffle 代入は元の単体の次数移送である（Berger–Fresse §1.1.3）。
方針：arity の移送を頂点の置換の共役で表し、垂直座標と置換の左単位則を使う。
規約：等式の両辺は単体次数 0+q に置く。
使われ方：左単位の shuffle 和を生成元の次数移送へ直す。 -/
lemma shuffleSimplex_left_unit (n q : ℕ) (s : ShufflePath 0 q)
    (y : (simplicial n) _⦋q⦌) :
    (simplicialArityMap (Nat.zero_add n)).app _ (shuffleSimplex 0 n 0 s unitSimplex y) =
      (simplicial n).map (degreeCastMap (Nat.zero_add q)).op y := by
  apply (simplexEquiv n (0 + q)).injective
  funext k
  simp only [simplexEquiv_arityMap, simplexEquiv_shuffleSimplex, simplexEquiv_map]
  have hv : s.vertical k = (degreeCastMap (Nat.zero_add q)).toOrderHom k :=
    Fin.ext (s.vertical_leftZero_val k)
  rw [hv]
  apply Equiv.ext
  intro z
  change Fin.cast (Nat.zero_add n)
      (permutationComposition 0 n 0 1
        (simplexEquiv n q y ((degreeCastMap (Nat.zero_add q)).toOrderHom k))
        (Fin.cast (Nat.zero_add n).symm z)) =
    simplexEquiv n q y ((degreeCastMap (Nat.zero_add q)).toOrderHom k) z
  exact permutationComposition_left_unit n _ (Fin.cast (Nat.zero_add n).symm z)

variable (A : Type u) [CommRing A]

/-- 概要：単位単体への shuffle 和は arity と次数の移送後に元の生成元になる（Berger–Fresse §1.1.3）。
方針：水平次数0の経路の一意性と符号1、正規化生成元の自然性を使う。
規約：arity の移送の後に鎖次数の移送を行う。
使われ方：正規化鎖上の左単位則の生成元の等式となる。 -/
lemma shuffleValue_left_unit (n q : ℕ) (y : (simplicial n) _⦋q⦌) :
    degreeTransport A n (Nat.zero_add q)
        ((normalizedChainMap A (simplicialArityMap (Nat.zero_add n))).f (0 + q)
          (shuffleValue A 0 n 0 0 q unitSimplex y)) = normalizedGenerator A n q y := by
  let _ : Unique (ShufflePath 0 q) := {
    default := zeroLeftPath q
    uniq := fun s => s.leftZero_unique (zeroLeftPath q) }
  simp only [shuffleValue, Fintype.sum_unique, ShufflePath.sign_leftZero, Units.val_one, one_smul,
    normalizedChainMap_generator, shuffleSimplex_left_unit, degreeTransport_generator_degreeCast]

/-- 概要：任意の正規化鎖を単位生成元へ代入すると移送後に元へ戻る（Berger–Fresse §1.1.3）。
方針：第二の入力に関する線形写像を生成元で恒等写像と比較する。
規約：arity n と鎖次数 q は任意である。
使われ方：複体の射の左単位則を成分で計算する。 -/
lemma shuffleBilinear_left_unit (n q : ℕ) (y : (normalizedChains A n).X q) :
    degreeTransport A n (Nat.zero_add q)
        ((normalizedChainMap A (simplicialArityMap (Nat.zero_add n))).f (0 + q)
          (shuffleBilinear A 0 n 0 0 q (normalizedGenerator A 1 0 unitSimplex) y)) = y := by
  let L := (degreeTransport A n (Nat.zero_add q)).comp
    (((normalizedChainMap A (simplicialArityMap (Nat.zero_add n))).f (0 + q)).hom.comp
      (shuffleBilinear A 0 n 0 0 q (normalizedGenerator A 1 0 unitSimplex)))
  have hL : L = LinearMap.id := by
    have hM : ModuleCat.ofHom L = 𝟙 ((normalizedChains A n).X q) := by
      apply normalizedGenerator_hom_ext A n q
      intro sy
      change degreeTransport A n (Nat.zero_add q)
        ((normalizedChainMap A (simplicialArityMap (Nat.zero_add n))).f (0 + q)
          (shuffleBilinear A 0 n 0 0 q (normalizedGenerator A 1 0 unitSimplex)
            (normalizedGenerator A n q sy))) = normalizedGenerator A n q sy
      rw [shuffleBilinear_generators]
      exact shuffleValue_left_unit A n q sy
    exact congrArg (fun f => f.hom) hM
  exact congrArg (fun f => f y) hL

end SerrePositivity.EInfinity.BarrattEccles
