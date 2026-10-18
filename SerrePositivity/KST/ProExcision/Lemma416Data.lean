module
public import SerrePositivity.KST.ProExcision.RightColumnInsertion

/-!
# Lemma 4.16 の帰納法の μ 版入力データ

概要：実ブロック群と右乗法から採用済み A.5 の P,Q,H,μ,α,β を構成する。
方針：第一入力を小さい右乗法、第二入力を Q の恒等射にする。
規約：KST Lemma 4.16 の非可換再記述と A.5 の augmentation 補正。
使われ方：因子内の帰納仮定を A.5 の実ホモトピーへ渡す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：Lemma 4.16 の帰納段階の実 P,Q,H,μ,α,β。
方針：実ブロック群の積の準同型と、小さい右乗法・恒等射を束ねる。
規約：KST A.5 の μ 版、入力の値域を各因子に保つ。
使われ方：非可換な実群の帰納法の A.5 への適用。 -/
def lemma416GroupData (n m : ℕ) (J : TwoSidedIdeal R) (a : R) :
    GroupProductData (Multiplicative (Fin n → J)) (triangularBlockGroup n (m + 1) J)
      (Multiplicative (Fin n → J)) (triangularBlockGroup n (m + 2) J) where
  μ := triangularBlockProductHom n (m + 1) J (Fin.castAdd (m + 1))
    (by intro i; exact i.isLt) (auxiliaryBlockIndex n m) (by change n ≤ n + m; omega)
  α := lastRightColumnHom n m J a
  β := MonoidHom.id _

/-- 概要：μ 版 A.5 の第一項は大きい群での右乗法 φ。
方針：第二因子の単位を消し、実挿入による右乗法の因子化を使う。
規約：KST 4.16。使われ方：補正和の第一項の端点の同定。 -/
lemma lemma416GroupData_left (n m : ℕ) (J : TwoSidedIdeal R) (a : R) :
    (lemma416GroupData n m J a).left = lastRightColumnHom n (m + 1) J a := by
  apply MonoidHom.ext
  intro v
  change triangularBlockGroupInsertion n (m + 1) J (auxiliaryBlockIndex n m)
      (lastRightColumnHom n m J a v) *
      (idealBlockColumnHom n (m + 2) J ((auxiliaryBlockIndex n m).succAbove ∘ Fin.castAdd (m + 1))
        (auxiliaryBlockIndex n m)
        (insertion_first_rows_lt n (m + 1) (Fin.castAdd (m + 1)) (fun i ↦ i.isLt)
          (auxiliaryBlockIndex n m) (by change n ≤ n + m; omega))
        (by change n ≤ n + m; omega) 1) = _
  rw [map_one, mul_one]
  exact congrArg (fun f ↦ f v) (triangularInsertion_lastRightColumn n m J a)

/-- 概要：μ 版 A.5 の第二項は補助列 ψ。
方針：第一因子の単位を消し、挿入後の first n 行の配置を同定する。
規約：KST 4.16。使われ方：補正和の第二項の端点の同定。 -/
lemma lemma416GroupData_right (n m : ℕ) (J : TwoSidedIdeal R) (a : R) :
    (lemma416GroupData n m J a).right = auxiliaryBlockColumnHom n m J := by
  apply MonoidHom.ext
  intro v
  change triangularBlockGroupInsertion n (m + 1) J (auxiliaryBlockIndex n m) 1 * _ = _
  rw [map_one, one_mul]
  apply Subtype.ext
  apply Units.ext
  change 1 + blockColumn ((auxiliaryBlockIndex n m).succAbove ∘ Fin.castAdd (m + 1))
    (auxiliaryBlockIndex n m) (fun i ↦ (v.toAdd i : R)) =
      1 + blockColumn (Fin.castAdd (m + 2)) (auxiliaryBlockIndex n m) (fun i ↦ (v.toAdd i : R))
  rw [show (auxiliaryBlockIndex n m).succAbove ∘ Fin.castAdd (m + 1) = Fin.castAdd (m + 2) from
    funext (auxiliaryInsertion_first_rows n m)]

/-- 概要：A.5 の積の準同型は補助元による ψ の共役に等しい。
方針：両因子の像の可換性で積の順序を合わせ、実共役公式を使う。
規約：KST 4.16、非可換な H を保つ。φ の積の順序は右乗法。
使われ方：A.6 の終点と A.5 の始点を連結する。 -/
lemma lemma416GroupData_product (n m : ℕ) (J : TwoSidedIdeal R) (a : J) :
    (lemma416GroupData n m J (a : R)).product =
      (inverseConjugation (auxiliaryBlockUnit n m J a)).comp (auxiliaryBlockColumnHom n m J) := by
  apply MonoidHom.ext
  intro v
  have h := (lemma416GroupData n m J (a : R)).images_commute
    (lastRightColumnHom n m J a v) v
  change Commute ((lemma416GroupData n m J (a : R)).left v)
    ((lemma416GroupData n m J (a : R)).right v) at h
  rw [lemma416GroupData_left, lemma416GroupData_right] at h
  rw [GroupProductData.product_apply, lemma416GroupData_left, lemma416GroupData_right]
  change _ = (auxiliaryBlockUnit n m J a)⁻¹ * auxiliaryBlockColumnHom n m J v * auxiliaryBlockUnit n m J a
  rw [auxiliaryBlockUnit_conjugation]
  change lastRightColumnHom n (m + 1) J a v * auxiliaryBlockColumnHom n m J v =
    auxiliaryBlockColumnHom n m J v * lastRightColumnHom n (m + 1) J a v
  exact h.eq

end SerrePositivity.KST.ProExcision
