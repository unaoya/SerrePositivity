module

public import SerrePositivity.EInfinity.BarrattEccles.Unit
public import SerrePositivity.EInfinity.BarrattEccles.PermutationUnit
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleZeroPaths

/-!
# shuffle 部分合成の右単位の計算

概要：Berger–Fresse §1.1.3 の恒等置換の0単体を代入する shuffle を計算する。
方針：垂直次数0の経路の一意性と符号1を使い、頂点ごとの置換の右単位則を適用する。
規約：外側の入力位置 i は任意である。
使われ方：部分合成の複体の射の右単位則を純粋テンソルで検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped Simplicial

/-- 概要：右に単位単体を入れた shuffle 単体は元の単体である（Berger–Fresse §1.1.3）。
方針：水平座標が頂点番号そのものであることと置換の右単位則を使う。
規約：垂直次数は0で、水平次数は任意である。
使われ方：右単位の shuffle 和の各項を計算する。 -/
lemma shuffleSimplex_right_unit (m : ℕ) (i : Fin (m + 1)) {p : ℕ}
    (s : ShufflePath p 0) (x : (simplicial (m + 1)) _⦋p⦌) :
    shuffleSimplex m 1 i s x unitSimplex = x := by
  apply (simplexEquiv (m + 1) p).injective
  funext k
  erw [simplexEquiv_shuffleSimplex m 1 i (p := p) (q := 0)]
  simp only [simplexEquiv_unitSimplex, permutationComposition_right_unit]
  rw [s.horizontal_rightZero]

variable (A : Type u) [CommRing A]

/-- 概要：右に単位単体を入れた shuffle 和は元の生成元である（Berger–Fresse §1.1.3）。
方針：垂直次数0の経路の一意性で有限和を一項にし、符号と単体を簡約する。
規約：退化単体も含む任意の単体について成立する。
使われ方：正規化鎖上の右単位則の生成元の等式となる。 -/
lemma shuffleValue_right_unit (m : ℕ) (i : Fin (m + 1)) (p : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) :
    shuffleValue A m 1 i p 0 x unitSimplex = normalizedGenerator A (m + 1) p x := by
  let _ : Unique (ShufflePath p 0) := {
    default := zeroRightPath p
    uniq := fun s => s.rightZero_unique (zeroRightPath p) }
  simp only [shuffleValue, Fintype.sum_unique, shuffleSimplex_right_unit,
    ShufflePath.sign_rightZero, Units.val_one, one_smul]
  rfl

/-- 概要：任意の正規化鎖へ右から単位生成元を代入すると元に戻る（Berger–Fresse §1.1.3）。
方針：第一の入力に関する線形写像を生成元で比較する。
規約：入力位置 i と鎖次数 p は任意である。
使われ方：複体の射の右単位則を成分で計算する。 -/
lemma shuffleBilinear_right_unit (m : ℕ) (i : Fin (m + 1)) (p : ℕ)
    (x : (normalizedChains A (m + 1)).X p) :
    shuffleBilinear A m 1 i p 0 x (normalizedGenerator A 1 0 unitSimplex) = x := by
  let L := (shuffleBilinear A m 1 i p 0).flip (normalizedGenerator A 1 0 unitSimplex)
  have hL : L = LinearMap.id := by
    have hM : ModuleCat.ofHom L = 𝟙 ((normalizedChains A (m + 1)).X p) := by
      apply normalizedGenerator_hom_ext A (m + 1) p
      intro sx
      change shuffleBilinear A m 1 i p 0 (normalizedGenerator A (m + 1) p sx)
        (normalizedGenerator A 1 0 unitSimplex) = normalizedGenerator A (m + 1) p sx
      rw [shuffleBilinear_generators, shuffleValue_right_unit]
    exact congrArg (fun f => f.hom) hM
  exact congrArg (fun f => f x) hL

/-- 概要：右から単位のスカラー倍を代入した部分合成は元のスカラー倍である（Berger–Fresse §1.1.3）。
方針：単位の射の0次の値を使い、負の純粋テンソルの公式を正規化鎖上の右単位則へ帰着する。
規約：単位複体の元は0次の標準同型で A の元から指定する。
使われ方：部分合成の右単位則を右単位子のスカラー作用と比較する。 -/
lemma partialComposition_right_unit_tmul (m : ℕ) (i : Fin (m + 1)) (p : ℕ)
    (x : (complex A (m + 1)).X (-(p : ℤ))) (a : A) :
    (partialComposition A m 1 i).f (-(p : ℤ))
        (ιTensorObj (complex A (m + 1)) (complex A 1) (-(p : ℤ)) 0 (-(p : ℤ)) (by omega)
          (x ⊗ₜ[A] (unit A).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv a))) =
      a • x := by
  erw [partialComposition_neg_tmul A m 1 i p 0]
  rw [unit_zero_apply, map_smul]
  have hu : (complexXIso A 1 0).hom
      ((complexXIso A 1 0).inv (normalizedGenerator A 1 0 unitSimplex)) =
        normalizedGenerator A 1 0 unitSimplex :=
    congrArg (fun f => f (normalizedGenerator A 1 0 unitSimplex)) (complexXIso A 1 0).inv_hom_id
  rw [hu, map_smul, shuffleBilinear_right_unit, map_smul]
  have hx : (complexXIso A (m + 1) p).inv ((complexXIso A (m + 1) p).hom x) = x :=
    congrArg (fun f => f x) (complexXIso A (m + 1) p).hom_inv_id
  exact congrArg (fun z => a • z) hx

end SerrePositivity.EInfinity.BarrattEccles
