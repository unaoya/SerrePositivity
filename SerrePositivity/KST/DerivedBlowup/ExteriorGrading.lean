module

public import SerrePositivity.KST.DerivedBlowup.ChartExterior
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
概要：KST Def3.1 の Koszul 外積模型の収縮が外積次数を一つ下げることを証明する。
方針：外積冪を生成元の像の部分加群冪として扱い、生成元の左乗法で帰納する。
規約：第n外積は後に cochain 次数−nへ置く。正則性や有限生成性は不要。
使われ方：チャートの整数次数 Koszul 複体と次数付き遷移写像を構成する。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- 概要：第0外積の収縮は零。
方針：第0外積の元は基底環の係数の像であることを使う。
規約：KST Def3.1 の Koszul 微分。使われ方：複体の次数0での境界条件。 -/
theorem exteriorContraction_zero_degree (d : M →ₗ[R] R) (z : ExteriorAlgebra R M)
    (hz : z ∈ ExteriorAlgebra.exteriorPower R 0 M) :
    CliffordAlgebra.contractLeft (Q := 0) d z = 0 := by
  change z ∈ (LinearMap.range (ExteriorAlgebra.ι R (M := M))) ^ 0 at hz
  rw [pow_zero] at hz
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hz
  exact CliffordAlgebra.contractLeft_algebraMap 0 d r

/-- 概要：収縮は第n+1外積を第n外積へ送る。
方針：第1外積では係数に送り、高次では左生成元の収縮公式と帰納法を使う。
規約：KST Def3.1、任意の可換基底環。使われ方：Koszul の次数ごとの微分を定義する。 -/
theorem exteriorContraction_mem_degree (d : M →ₗ[R] R) :
    ∀ (n : ℕ) (z : ExteriorAlgebra R M),
      z ∈ ExteriorAlgebra.exteriorPower R (n + 1) M →
        CliffordAlgebra.contractLeft (Q := 0) d z ∈ ExteriorAlgebra.exteriorPower R n M := by
  intro n
  induction n with
  | zero =>
    intro z hz
    change z ∈ (LinearMap.range (ExteriorAlgebra.ι R (M := M))) ^ 1 at hz
    rw [pow_one] at hz
    obtain ⟨m, rfl⟩ := hz
    rw [CliffordAlgebra.contractLeft_ι]
    exact Submodule.algebraMap_mem (d m)
  | succ n ih =>
    intro z hz
    change z ∈ (LinearMap.range (ExteriorAlgebra.ι R (M := M))) ^ (n + 2) at hz
    rw [pow_succ'] at hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro m hm y hy
      obtain ⟨m, rfl⟩ := hm
      rw [CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ (d m) hy
      · have hdy := ih y hy
        have hm : ExteriorAlgebra.ι R m ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M)) :=
          LinearMap.mem_range_self _ m
        simpa only [ExteriorAlgebra.exteriorPower, pow_succ'] using Submodule.mul_mem_mul hm hdy
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz

/-- 概要：第n+1外積から第n外積への実際の線形微分。
方針：全外積代数の収縮を部分加群に制限する。
規約：KST Def3.1、次数は homological。使われ方：外積 Koszul 複体の射。 -/
def exteriorDegreeDifferential (d : M →ₗ[R] R) (n : ℕ) :
    ExteriorAlgebra.exteriorPower R (n + 1) M →ₗ[R] ExteriorAlgebra.exteriorPower R n M :=
  ((CliffordAlgebra.contractLeft (Q := 0) d).comp
    (ExteriorAlgebra.exteriorPower R (n + 1) M).subtype).codRestrict _
      (fun z => exteriorContraction_mem_degree d n z.val z.property)

/-- 概要：次数ごとの微分も二回の合成が零。
方針：部分加群への包含の単射性で全外積上の平方零へ帰着する。
規約：KST Def3.1。使われ方：外積 Koszul 複体の構成に必要な複体律。 -/
theorem exteriorDegreeDifferential_sq (d : M →ₗ[R] R) (n : ℕ)
    (z : ExteriorAlgebra.exteriorPower R (n + 2) M) :
    exteriorDegreeDifferential d n (exteriorDegreeDifferential d (n + 1) z) = 0 := by
  apply Subtype.ext
  exact CliffordAlgebra.contractLeft_contractLeft d z.val

end SerrePositivity.KST.DerivedBlowup
