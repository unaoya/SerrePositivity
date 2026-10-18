module
public import SerrePositivity.KST.ProExcision.TriangularBlockProduct

/-!
# 右乗法を実三角ブロック群の最後の列に入れる

概要：イデアル内の列ベクトルに右乗法を施し、最後の列に埋める実群準同型を作る。
方針：両側イデアルの右吸収、加法性、実補助列の準同型を合成する。
規約：KST Lemma 4.16 の非可換版 φ(v)=va。中心性はここでは不要。
使われ方：帰納法の入力 α と大きい群内の φ を同じ定義で与える。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：イデアル上の右乗法の加法群準同型。
方針：右分配法則と両側イデアルの右吸収を使う。
規約：KST 4.16、右乗法の順序を保つ。
使われ方：列ベクトルの右乗法の構成。 -/
def idealRightMultiplication (J : TwoSidedIdeal R) (a : R) : J →+ J where
  toFun x := ⟨(x : R) * a, J.mul_mem_right _ _ x.property⟩
  map_zero' := by apply Subtype.ext; exact zero_mul a
  map_add' x y := by apply Subtype.ext; exact add_mul (x : R) (y : R) a

/-- 概要：イデアル内の列ベクトルへの右乗法の群準同型。
方針：各成分の右乗法の加法群準同型を乗法タグへ移す。
規約：KST Lemma 4.16、中心性・単射性は不要。
使われ方：帰納仮定と同じ φ を因子内に値を持つ準同型として定義する。 -/
def idealVectorRightHom (J : TwoSidedIdeal R) (ι : Type v) (a : R) :
    Multiplicative (ι → J) →* Multiplicative (ι → J) :=
  (show (ι → J) →+ (ι → J) from
    { toFun := fun v i ↦ idealRightMultiplication J a (v i)
      map_zero' := by funext i; exact map_zero (idealRightMultiplication J a)
      map_add' := by intro v w; funext i; exact map_add (idealRightMultiplication J a) (v i) (w i) }).toMultiplicative

/-- 概要：first n 行は最後の補助列より前にある。
方針：行の添字の上界から自然数の不等式を示す。
規約：KST 4.16、補助列が少なくとも一つある場合。
使われ方：最後の列の三角条件。 -/
lemma firstRows_lt_last (n m : ℕ) (i : Fin n) :
    Fin.castAdd (m + 1) i < (Fin.last (n + m) : Fin (n + (m + 1))) := by
  change i.val < n + m
  omega

/-- 概要：イデアル内の列ベクトルを実三角ブロック群の最後の列に入れる準同型。
方針：補助列の準同型を最後の列と first n 行に特殊化する。
規約：KST Lemma 4.16 の加法群の埋め込み。
使われ方：右乗法を前合成して φ を与える。 -/
def lastBlockColumnHom (n m : ℕ) (J : TwoSidedIdeal R) :
    Multiplicative (Fin n → J) →* triangularBlockGroup n (m + 1) J :=
  idealBlockColumnHom n (m + 1) J (Fin.castAdd (m + 1)) (Fin.last (n + m))
    (firstRows_lt_last n m) (by change n ≤ n + m; omega)

/-- 概要：右乗法 φ(v)=va を最後の列に入れる実群準同型。
方針：イデアル内の列の右乗法と最後の列の埋め込みを合成する。
規約：KST Lemma 4.16 の非可換再記述、値域は T_{n,m+1}(I)。
使われ方：m 次で定数と比較する帰納法の対象。 -/
def lastRightColumnHom (n m : ℕ) (J : TwoSidedIdeal R) (a : R) :
    Multiplicative (Fin n → J) →* triangularBlockGroup n (m + 1) J :=
  (lastBlockColumnHom n m J).comp (idealVectorRightHom J (Fin n) a)

end SerrePositivity.KST.ProExcision
