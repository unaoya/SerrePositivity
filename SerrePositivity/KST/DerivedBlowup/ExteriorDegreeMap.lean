module

public import SerrePositivity.KST.DerivedBlowup.ExteriorComplex

/-!
概要：KST Def3.1 の Koszul 生成元の線形変換を各外積次数へ制限する。
方針：第n外積の span 表示と外積写像の普遍性を使う。
規約：同一可換環上の線形写像。係数環を変える場合の導来底変更とは区別する。
使われ方：チャート重なりの Koszul 複体の同型と cocycle。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R]
  {M N P : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- 概要：外積写像は第n外積を保つ。
方針：n個の生成元の積による span 表示で確認する。
規約：KST Def3.1 の基底変換。使われ方：全外積上の環射を次数別に制限する。 -/
theorem exteriorMap_mem_degree (f : M →ₗ[R] N) (n : ℕ) (z : ExteriorAlgebra R M)
    (hz : z ∈ ExteriorAlgebra.exteriorPower R n M) :
    ExteriorAlgebra.map f z ∈ ExteriorAlgebra.exteriorPower R n N := by
  have hle : ExteriorAlgebra.exteriorPower R n M ≤
      (ExteriorAlgebra.exteriorPower R n N).comap (ExteriorAlgebra.map f).toLinearMap := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    change ExteriorAlgebra.map f (ExteriorAlgebra.ιMulti R n m) ∈
      ExteriorAlgebra.exteriorPower R n N
    rw [ExteriorAlgebra.map_apply_ιMulti]
    exact ExteriorAlgebra.ιMulti_range R n ⟨_, rfl⟩
  exact hle hz

/-- 概要：生成元写像の第n外積への線形な制限。
方針：外積代数写像を部分加群に制限する。
規約：KST Def3.1。使われ方：Koszul 複体の次数別成分。 -/
def exteriorDegreeMap (f : M →ₗ[R] N) (n : ℕ) :
    ExteriorAlgebra.exteriorPower R n M →ₗ[R] ExteriorAlgebra.exteriorPower R n N :=
  ((ExteriorAlgebra.map f).toLinearMap.comp
    (ExteriorAlgebra.exteriorPower R n M).subtype).codRestrict _
      (fun z => exteriorMap_mem_degree f n z.val z.property)

/-- 概要：次数別外積写像は合成を保つ。
方針：部分加群への包含を通じて全外積の関手性を使う。
規約：KST §3.1 の三重重なり。使われ方：複体の射の cocycle。 -/
theorem exteriorDegreeMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    (exteriorDegreeMap g n).comp (exteriorDegreeMap f n) =
      exteriorDegreeMap (g.comp f) n := by
  ext z
  exact AlgHom.congr_fun (ExteriorAlgebra.map_comp_map f g) z.val

/-- 概要：恒等生成元写像の第n外積は恒等。
方針：全外積の map_id を使う。規約：KST Def3.1。
使われ方：次数別基底同型の両側逆。 -/
@[simp] theorem exteriorDegreeMap_id (n : ℕ) :
    exteriorDegreeMap (LinearMap.id : M →ₗ[R] M) n = LinearMap.id := by
  ext z
  exact AlgHom.congr_fun ExteriorAlgebra.map_id z.val

/-- 概要：微分に適合する生成元写像は全外積の収縮と可換。
方針：係数・和・生成元による左乗法で帰納する。
規約：KST Def3.1、dN∘f=dM が微分適合条件。
使われ方：任意の可逆 Koszul 基底変換を複体の同型へ持ち上げる。 -/
theorem exteriorContraction_map (f : M →ₗ[R] N) (dM : M →ₗ[R] R) (dN : N →ₗ[R] R)
    (h : dN.comp f = dM) (z : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := 0) dN (ExteriorAlgebra.map f z) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (Q := 0) dM z) := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | ι_mul z m hz =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
      ExteriorAlgebra.map_apply_ι, hz]
    have hm := LinearMap.congr_fun h m
    exact congrArg (fun c => c • ExteriorAlgebra.map f z -
      ExteriorAlgebra.ι R (f m) * ExteriorAlgebra.map f
        (CliffordAlgebra.contractLeft (Q := 0) dM z)) hm

end SerrePositivity.KST.DerivedBlowup
