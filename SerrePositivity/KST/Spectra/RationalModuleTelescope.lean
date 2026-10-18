module

public import SerrePositivity.KST.Spectra.RationalTelescopeCoefficients
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
概要：アーベル群の乗法列 2,3,4,… の加群としての直極限。
方針：区間係数のスカラー写像を directed system とし、分母の共終性から非零整数の可逆性を示す。
規約：群は加法記法の ℤ 加群。スペクトルの telescope 自体とは区別する。
使われ方：BF 1978 §2、HA §1.4.2。L9d の telescope のホモトピー群の計算先。
-/

@[expose] public section

universe u

namespace SerrePositivity.KST.Spectra.RationalTelescope

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : Type u) [AddCommGroup A]

/-- 概要：乗法列の二段間の ℤ 線形遷移写像。
方針：区間係数を恒等線形写像へ掛ける。
規約：順序の証明自体には依存しない。
使われ方：HA §1.4.2。有理化の群の directed system。 -/
def scalarTransition (i j : ℕ) (_ : i ≤ j) : A →ₗ[ℤ] A :=
  integerCoefficient i j • LinearMap.id

/-- 概要：乗法列の線形遷移は directed system の条件を満たす。
方針：区間係数の恒等式・合成式をスカラー作用へ移す。
規約：元の加群 A にねじれがあってもよい。
使われ方：HA §1.4.2。直極限の等式の後続段での検出。 -/
instance scalarTransition_directed : DirectedSystem (fun _ : ℕ ↦ A) (scalarTransition A · · ·) where
  map_self x := by simp [scalarTransition]
  map_map {k j i} hij hjk x := by
    change integerCoefficient j k • (integerCoefficient i j • (x : A)) = integerCoefficient i k • x
    rw [smul_smul, integerCoefficient_comp hij hjk]

/-- 概要：乗法列の加法群の直極限。
方針：線形遷移の Module.DirectLimit を使う。
規約：まだ ℚ テンソルとの同型を定義に含めない。
使われ方：HA §1.4.2。有理化の群の実構成。 -/
abbrev additiveLimit : Type u := Module.DirectLimit (fun _ : ℕ ↦ A) (scalarTransition A)

/-- 概要：乗法列の一つの段から直極限への標準線形写像。
方針：加群の直極限への標準加法射を、標準の ℤ 加群構造で線形化する。
規約：零段も含む全自然数 i。
使われ方：HA §1.4.2。直極限の元の代表。 -/
def inclusion (i : ℕ) : A →ₗ[ℤ] additiveLimit A :=
  (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ ↦ A) (scalarTransition A) i).toAddMonoidHom.toIntLinearMap

/-- 概要：直極限の標準射は乗法遷移を打ち消す。
方針：Module.DirectLimit の標準関係を使う。
規約：i≤j。
使われ方：HA §1.4.2。分母を変えた代表の同一視。 -/
@[simp]
theorem inclusion_transition {i j : ℕ} (hij : i ≤ j) (a : A) :
    inclusion A j (integerCoefficient i j • a) = inclusion A i a :=
  Module.DirectLimit.of_f (f := scalarTransition A) (hij := hij) (x := a)

/-- 概要：直極限の任意の元は一つの段の元で表せる。
方針：自然数の有向性と加群の直極限の代表表示を使う。
規約：複数段の和も一つの後続段へ移せる。
使われ方：HA §1.4.2。局所化の分数表示の証明。 -/
theorem exists_inclusion (y : additiveLimit A) : ∃ i a, inclusion A i a = y :=
  Module.DirectLimit.exists_of y

/-- 概要：同じ段の二つの代表が直極限で等しければ一つの後続段で等しい。
方針：directed system の直極限の関係の検出を使う。
規約：後続段の比較は区間係数の乗法である。
使われ方：HA §1.4.2。ねじれと分母の消去の検出。 -/
theorem inclusion_eq_eventually (i : ℕ) (a b : A)
    (h : inclusion A i a = inclusion A i b) :
    ∃ j, i ≤ j ∧ integerCoefficient i j • a = integerCoefficient i j • b := by
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  exact ⟨j, hij, hj⟩

/-- 概要：直極限では全ての非零整数のスカラー作用は全射。
方針：元の段から十分先の遷移係数を指定整数の倍数に取り、その商を代表へ掛ける。
規約：元の A には可除性を仮定しない。
使われ方：HA §1.4.2。乗法列の直極限が有理化であることの可除性。 -/
theorem additiveLimit_smul_surjective (m : ℤ) (hm : m ≠ 0) :
    Function.Surjective (fun y : additiveLimit A ↦ m • y) := by
  intro y
  obtain ⟨i, a, rfl⟩ := exists_inclusion A y
  obtain ⟨j, hij, q, hq⟩ := exists_dvd_integerCoefficient i m hm
  refine ⟨inclusion A j (q • a), ?_⟩
  change m • inclusion A j (q • a) = inclusion A i a
  rw [← (inclusion A j).map_smul m (q • a), smul_smul, ← hq]
  exact inclusion_transition A hij a

/-- 概要：直極限では全ての非零整数のスカラー作用は単射。
方針：ねじれを検出した段のさらに先で遷移係数を指定整数の倍数に取り、分母を消す。
規約：元の A のねじれは直極限で消える。
使われ方：HA §1.4.2。乗法列の直極限の一意可除性。 -/
theorem additiveLimit_smul_injective (m : ℤ) (hm : m ≠ 0) :
    Function.Injective (fun y : additiveLimit A ↦ m • y) := by
  intro y z h
  obtain ⟨i, a, b, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ y z
  have h' : inclusion A i (m • a) = inclusion A i (m • b) := by
    change m • inclusion A i a = m • inclusion A i b at h
    rw [← (inclusion A i).map_smul m a, ← (inclusion A i).map_smul m b] at h
    exact h
  obtain ⟨j, hij, hj⟩ := inclusion_eq_eventually A i (m • a) (m • b) h'
  obtain ⟨k, hjk, q, hq⟩ := exists_dvd_integerCoefficient j m hm
  have heq := congrArg (fun v : A ↦ q • v) hj
  simp only [smul_smul] at heq
  have hcoeff : integerCoefficient i k = q * (integerCoefficient i j * m) := by
    rw [integerCoefficient_comp hij hjk, hq]
    ac_rfl
  rw [← hcoeff] at heq
  calc
    inclusion A i a = inclusion A k (integerCoefficient i k • a) :=
      (inclusion_transition A (hij.trans hjk) a).symm
    _ = inclusion A k (integerCoefficient i k • b) := congrArg (inclusion A k) heq
    _ = inclusion A i b := inclusion_transition A (hij.trans hjk) b

/-- 概要：直極限では全ての非零整数の乗法は全単射。
方針：構成済みの単射性と全射性を束ねる。
規約：零でない負の整数も含む。
使われ方：HA §1.4.2。加群の局所化と ℚ テンソルの比較。 -/
theorem additiveLimit_smul_bijective (m : ℤ) (hm : m ≠ 0) :
    Function.Bijective (fun y : additiveLimit A ↦ m • y) :=
  ⟨additiveLimit_smul_injective A m hm, additiveLimit_smul_surjective A m hm⟩

end

end SerrePositivity.KST.Spectra.RationalTelescope
