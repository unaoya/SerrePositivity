module
public import SerrePositivity.KST.ProExcision.MatrixActionInsertion
public import SerrePositivity.KST.ProExcision.Lemma416Data

/-!
# Lemma 4.16 の μ 版データの全行列同変性

概要：実 P,Q,H,μ,α,β の各射が構成した全行列モノイド作用と可換である。
方針：ブロック挿入と実列の同変性を μ の積へ移す。
規約：KST Lemma 4.16 の非可換再記述と Construction A.5 の明示的な因子内データ。
使われ方：帰納仮定と Q の0次比較を同変な A.5 へ渡す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：帰納法の μ は実埋め込みと補助列の像の積。
方針：第二項の実同定から Q の射を同定する。
規約：KST 4.16、非可換な H 内の積。
使われ方：μ の全行列同変性。 -/
lemma lemma416GroupData_mu_apply (n m : ℕ) (J : TwoSidedIdeal R) (a : R)
    (p : triangularBlockGroup n (m + 1) J) (q : Multiplicative (Fin n → J)) :
    (lemma416GroupData n m J a).μ (p, q) =
      triangularBlockGroupInsertion n (m + 1) J (auxiliaryBlockIndex n m) p * auxiliaryBlockColumnHom n m J q := by
  have hq := congrArg (fun f ↦ f q) (lemma416GroupData_right n m J a)
  change triangularBlockGroupInsertion n (m + 1) J (auxiliaryBlockIndex n m) 1 * _ = _ at hq
  rw [map_one, one_mul] at hq
  dsimp only [MonoidHom.prod_apply, lemma416GroupData, MonoidHom.id_apply] at hq
  change triangularBlockGroupInsertion n (m + 1) J (auxiliaryBlockIndex n m) p * _ = _
  rw [hq]

/-- 概要：μ は実ブロック群の全行列作用に同変。
方針：実埋め込みと補助列の同変性と、群自己準同型の積の保存を使う。
規約：KST A.5・4.16、非可逆な M と非可換な H。
使われ方：採用済み μ 版 A.5 の外部 G の条件。 -/
lemma lemma416GroupData_mu_equivariant (n m : ℕ) (J : TwoSidedIdeal R) (a : R)
    (M : Matrix (Fin n) (Fin n) R) (p : triangularBlockGroup n (m + 1) J)
    (q : Multiplicative (Fin n → J)) :
    (lemma416GroupData n m J a).μ
      (triangularBlockMatrixAction n (m + 1) J M p, idealMatrixAction n J M q) =
    triangularBlockMatrixAction n (m + 2) J M ((lemma416GroupData n m J a).μ (p, q)) := by
  rw [lemma416GroupData_mu_apply, lemma416GroupData_mu_apply,
    triangularBlockInsertion_equivariant n (m + 1) J _ (by change n ≤ n + m; omega),
    auxiliaryBlockColumnHom_equivariant, map_mul]

/-- 概要：帰納法の全ての実群データと射を全行列同変な A.5 データに束ねる。
方針：α の右乗法、β の恒等性、μ の積の同変性を使う。
規約：KST A.5 の μ 版と Lemma 4.16、結論のホモトピーは仮定しない。
使われ方：帰納仮定の同変性を A.5 の入力へ渡す。 -/
def lemma416EquivariantGroupData (n m : ℕ) (J : TwoSidedIdeal R) (a : R) :
    EquivariantGroupProductData (idealMatrixAction n J) (triangularBlockMatrixAction n (m + 1) J)
      (idealMatrixAction n J) (triangularBlockMatrixAction n (m + 2) J) where
  toGroupProductData := lemma416GroupData n m J a
  α_equivariant := lastRightColumnHom_equivariant n m J a
  β_equivariant := by intro M v; rfl
  μ_equivariant := lemma416GroupData_mu_equivariant n m J a

end SerrePositivity.KST.ProExcision
