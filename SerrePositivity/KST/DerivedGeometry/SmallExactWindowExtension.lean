module

public import SerrePositivity.KST.DerivedGeometry.UniformGeneratorEpiCover
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
概要：完全な短複体内の部分窓を、一つ前の次数の小さい部分対象で完全に延長する。
方針：部分窓の核を全体の cycles に持ち上げ、全射の pullback と小さい全射部分対象を取る。
規約：生成対象の projectivity は使わない。
使われ方：Stacks Lemma 19.12.2 (079K)、TT §3・§8、Toën §3.2 の小さい非輪状部分複体の帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：完全な短複体に埋め込まれた隣接二項を、小さい先行項で完全に延長できる。
方針：核への全射を pullback し、統一した直和の商としての全射部分対象を構成する。
規約：先行項の直和の上界は中央項を呈示する固定対象だけで決まる。
使われ方：Stacks 19.12.2、TT §3 の小さい上に有界な非輪状部分複体。
-/
lemma exists_small_exact_window_extension (G : C) (hG : IsSeparator G)
    (B : ShortComplex C) (hB : B.Exact) {A₁ A₂ Q : C}
    (d : A₁ ⟶ A₂) (j₁ : A₁ ⟶ B.X₂) [Mono j₁]
    (j₂ : A₂ ⟶ B.X₃) [Mono j₂] (comm : d ≫ j₂ = j₁ ≫ B.g)
    (q : Q ⟶ A₁) [Epi q] :
    ∃ (A₀ : C) (a : (∐ fun _ : Shrink.{w} (Subobject Q) => G) ⟶ A₀)
      (d₀ : A₀ ⟶ A₁) (j₀ : A₀ ⟶ B.X₁), Epi a ∧ Mono j₀ ∧
      d₀ ≫ j₁ = j₀ ≫ B.f ∧ ∃ hz : d₀ ≫ d = 0, (ShortComplex.mk d₀ d hz).Exact := by
  have ht : Epi B.toCycles := hB.epi_toCycles
  have hz : (kernel.ι d ≫ j₁) ≫ B.g = 0 := by
    rw [Category.assoc, ← comm, ← Category.assoc, kernel.condition, zero_comp]
  let k : kernel d ⟶ B.cycles := B.liftCycles (kernel.ι d ≫ j₁) hz
  have hk : k ≫ B.iCycles = kernel.ι d ≫ j₁ := B.liftCycles_i _ hz
  have : Mono (k ≫ B.iCycles) := by rw [hk]; infer_instance
  have : Mono k := mono_of_mono k B.iCycles
  let P := pullback B.toCycles k
  have : Epi (pullback.snd B.toCycles k) := inferInstance
  obtain ⟨A₀, a, i, ha, hi, he⟩ := exists_uniform_generator_epi_subobject G hG
    (pullback.snd B.toCycles k) (smallSubquotientEmbedding q (kernel.ι d))
  have : Epi a := ha
  have : Mono i := hi
  have : Epi (i ≫ pullback.snd B.toCycles k) := he
  let e := i ≫ pullback.snd B.toCycles k
  let d₀ := e ≫ kernel.ι d
  let j₀ := i ≫ pullback.fst B.toCycles k
  have hc : d₀ ≫ j₁ = j₀ ≫ B.f := by
    calc
      d₀ ≫ j₁ = i ≫ (pullback.snd B.toCycles k ≫ k) ≫ B.iCycles := by
        dsimp [d₀, e]
        simp only [Category.assoc, hk]
      _ = i ≫ (pullback.fst B.toCycles k ≫ B.toCycles) ≫ B.iCycles := by
        rw [pullback.condition]
      _ = j₀ ≫ B.f := by
        dsimp [j₀]
        simp only [Category.assoc, B.toCycles_i]
  have hz₀ : d₀ ≫ d = 0 := by simp [d₀, Category.assoc]
  refine ⟨A₀, a, d₀, j₀, ha, inferInstance, hc, hz₀, ?_⟩
  apply (ShortComplex.exact_iff_epi_kernel_lift _).mpr
  have hke : kernel.lift d d₀ hz₀ = e := by
    apply (cancel_mono (kernel.ι d)).mp
    simp [d₀]
  change Epi (kernel.lift d d₀ hz₀)
  rw [hke]
  infer_instance

end SerrePositivity.KST.DerivedGeometry
