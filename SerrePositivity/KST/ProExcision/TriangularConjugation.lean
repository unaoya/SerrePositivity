module
public import SerrePositivity.KST.ProExcision.ColumnInsertion
public import SerrePositivity.KST.ProExcision.GroupHomotopyOperations

/-!
# 実三角ブロック群内での Lemma 4.16 の共役

概要：補助元 u と ψ を実ブロック群内に構成し、u⁻¹ψ(v)u=ψ(v)φ(v) を証明する。
方針：係数イデアル内の単一成分行列を二乗零の単位にし、実列の共役公式を適用する。
規約：KST Lemma 4.16 の非可換再記述、右乗法 v_i a の順序。
使われ方：A.6 と μ 版 A.5 の m 次比較の中間射の同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：最後の列の直前の補助座標。
方針：n+m を n+m+2 の範囲の添字とする。
規約：KST 4.16 の n,m,1,1 の配置。
使われ方：ψ の列と u の行。 -/
def auxiliaryBlockIndex (n m : ℕ) : Fin (n + (m + 2)) := ⟨n + m, by omega⟩

/-- 概要：補助行から最後の列へ a を入れた実群内の単位 u。
方針：単一成分行列の二乗零と三角部分環の所属を使う。
規約：KST 4.16、非可換の係数イデアル J 内の a。
使われ方：A.6 の共役比較を同じ H 内で作る。 -/
def auxiliaryBlockUnit (n m : ℕ) (J : TwoSidedIdeal R) (a : J) :
    triangularBlockGroup n (m + 2) J := by
  let p := auxiliaryBlockIndex n m
  let q : Fin (n + (m + 2)) := Fin.last (n + m + 1)
  let U : Matrix (Fin (n + (m + 2))) (Fin (n + (m + 2))) R := Matrix.single p q (a : R)
  have hpq : q ≠ p := by
    intro h
    have hv := congrArg Fin.val h
    change n + m + 1 = n + m at hv
    omega
  have hU : U * U = 0 :=
    @Matrix.single_mul_single_of_ne _ _ _ R _ _ _ _ _ (a : R) p q p q hpq (a : R)
  have hmem : U ∈ blockPatternSubring (n + (m + 2)) n J :=
    single_mem_blockPattern _ n J p q a ⟨by change n + m < n + m + 1; omega,
      by change n ≤ n + m + 1; omega⟩ a.property
  exact ⟨squareZeroUnit U hU, squareZeroUnit_mem_oneDifference _ U hU hmem⟩

/-- 概要：最後の列の直前の補助列にベクトルを入れる実群準同型 ψ。
方針：first n 行と補助添字で実列の準同型を特殊化する。
規約：KST Lemma 4.16 の ψ、値域は T_{n,m+2}(I)。
使われ方：共役比較と μ 版 A.5 の第二の項。 -/
def auxiliaryBlockColumnHom (n m : ℕ) (J : TwoSidedIdeal R) :
    Multiplicative (Fin n → J) →* triangularBlockGroup n (m + 2) J :=
  idealBlockColumnHom n (m + 2) J (Fin.castAdd (m + 2)) (auxiliaryBlockIndex n m)
    (by intro i; change i.val < n + m; omega) (by change n ≤ n + m; omega)

/-- 概要：実三角ブロック群内の補助元による共役は ψ(v)φ(v)。
方針：単位と列の実成分を展開して証明済みの非可換行列の共役公式を使う。
規約：KST Lemma 4.16、φ(v)=va。I の可換性も a の中心性も不要。
使われ方：A.6 の実比較の終点を A.5 の積の始点に同定する。 -/
lemma auxiliaryBlockUnit_conjugation (n m : ℕ) (J : TwoSidedIdeal R) (a : J)
    (v : Multiplicative (Fin n → J)) :
    (auxiliaryBlockUnit n m J a)⁻¹ * auxiliaryBlockColumnHom n m J v * auxiliaryBlockUnit n m J a =
      auxiliaryBlockColumnHom n m J v * lastRightColumnHom n (m + 1) J a v := by
  apply Subtype.ext
  apply Units.ext
  exact blockColumn_conjugation (Fin.castAdd (m + 2)) (auxiliaryBlockIndex n m)
    (Fin.last (n + m + 1)) (fun i ↦ (v.toAdd i : R)) (a : R)
    (by intro h; have hv := congrArg Fin.val h; change n + m + 1 = n + m at hv; omega)
    (by intro i h; have hv := congrArg Fin.val h; change n + m = i.val at hv; omega)
    (by intro i h; have hv := congrArg Fin.val h; change n + m + 1 = i.val at hv; omega)

end SerrePositivity.KST.ProExcision
