module
public import SerrePositivity.KST.ProExcision.BlockPattern
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# 非単位環の整数単位化と係数イデアル

概要：非単位の結合環を整数単位化の両側イデアルとして扱う。
方針：整数成分への標準射影の核を使い、元の環からの包含の像と同定する。
規約：KST Lemma 4.16 の非可換な実行列の周囲単位環。
使われ方：T_{n,m}(I) の係数イデアルと補助元 a の型を具体化する。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable (I : Type u) [NonUnitalRing I]

/-- 概要：整数単位化内の元の非単位環に対応する両側イデアル。
方針：整数成分への準同型の核を取る。
規約：KST 4.16 の非可換な I の単位化。
使われ方：実ブロック行列の非自明な係数を指定する。 -/
def integerUnitizationIdeal : TwoSidedIdeal (Unitization ℤ I) :=
  TwoSidedIdeal.ker (Unitization.fstHom ℤ I)

/-- 概要：係数イデアルの元はちょうど整数成分が零である元。
方針：核の所属条件を展開する。
規約：KST 4.16、整数単位化の模型。
使われ方：元の I の元の包含と係数の確認。 -/
lemma mem_integerUnitizationIdeal (x : Unitization ℤ I) :
    x ∈ integerUnitizationIdeal I ↔ x.fst = 0 :=
  TwoSidedIdeal.mem_ker _

/-- 概要：元の非単位環の元は係数イデアルに属する。
方針：包含された元の整数成分は零。
規約：KST 4.16、単位化でのみ 1 を使用する。
使われ方：ψ と φ の列の成分が I 内であることの証明。 -/
lemma inr_mem_integerUnitizationIdeal (x : I) :
    (x : Unitization ℤ I) ∈ integerUnitizationIdeal I := by
  rw [mem_integerUnitizationIdeal]
  rfl

/-- 概要：係数イデアルは元の非単位環の包含の像と等しい。
方針：整数成分が零なら第二成分の包含と等しいことを外延性で示す。
規約：KST 4.16、非可換性を保持する実模型。
使われ方：イデアル内の行列成分を元の I の成分へ戻す。 -/
lemma mem_integerUnitizationIdeal_iff (x : Unitization ℤ I) :
    x ∈ integerUnitizationIdeal I ↔ ∃ a : I, (a : Unitization ℤ I) = x := by
  constructor
  · intro hx
    refine ⟨x.snd, ?_⟩
    apply Unitization.ext
    · exact ((mem_integerUnitizationIdeal I x).mp hx).symm
    · rfl
  · rintro ⟨a, rfl⟩
    exact inr_mem_integerUnitizationIdeal I a

/-- 概要：非単位環上の実三角ブロック群。
方針：整数単位化とその核イデアルで係数を指定する。
規約：KST Lemma 4.16 の T_{n,m}(I)、非可換な結合環。
使われ方：帰納法の P と H の実群模型。 -/
def nonUnitalTriangularBlockGroup (n m : ℕ) :
    Subgroup (Matrix (Fin (n + m)) (Fin (n + m)) (Unitization ℤ I))ˣ :=
  triangularBlockGroup n m (integerUnitizationIdeal I)

end SerrePositivity.KST.ProExcision
