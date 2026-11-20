module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Encodable

/-!
概要：KST §5、Stacks 05DP・059X で必要な有限型代数上の有限加群の基礎環上の可算生成性。
方針：多項式の単項式基底の像と有限個の加群生成元への作用像を使う。
規約：可算な生成集合を実際に存在量化し、基礎環自体の可算性は要求しない。
使われ方：平坦 Mittag–Leffler 加群の射影性判定へ有限型加群を渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：基礎環上可算個の元で生成される加群の条件。
方針：可算集合とその線形包が全体である等式を存在量化する。
規約：KST §5、Stacks 05DP・059X、基礎環と加群の宇宙は任意。
使われ方：有限型代数上の有限加群を可算生成の射影性判定へ接続する。
-/
def HasCountableGeneratingSet (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ S : Set M, S.Countable ∧ Submodule.span R S = ⊤

/--
概要：可算な添字を持つ基底は可算な生成集合を与える。
方針：基底の値域を取り、基底の生成性を使う。
規約：KST §5、Stacks 05DP・059X、係数環の集合としての可算性は不要。
使われ方：有限変数多項式環の単項式基底への適用。
-/
theorem hasCountableGeneratingSet_of_basis
    {R M κ : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Countable κ]
    (b : Module.Basis κ R M) : HasCountableGeneratingSet R M :=
  ⟨Set.range b, Set.countable_range b, b.span_eq⟩

/--
概要：可算な生成集合の全射線形像も可算な生成集合を持つ。
方針：生成集合の像を取り、線形包と線形像の可換性を使う。
規約：KST §5、Stacks 05DP・059X、線形写像の核の有限性は不要。
使われ方：多項式環から有限型代数への全射に適用する。
-/
theorem HasCountableGeneratingSet.of_surjective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hM : HasCountableGeneratingSet R M)
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : HasCountableGeneratingSet R N := by
  obtain ⟨S, hc, hs⟩ := hM
  refine ⟨f '' S, hc.image f, ?_⟩
  rw [← Submodule.map_span, hs, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/--
概要：有限型代数は基礎環上可算個の元で生成される。
方針：有限変数多項式環からの実際の全射を選び、可算な単項式基底の像を使う。
規約：KST §5、Stacks 05DP・059X、Noether 性と平坦性は不要。
使われ方：有限型代数上の有限加群の可算生成性の係数側。
-/
theorem hasCountableGeneratingSet_of_finiteType
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
    HasCountableGeneratingSet R B := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  exact (hasCountableGeneratingSet_of_basis (MvPolynomial.basisMonomials (Fin n) R)).of_surjective
    f.toLinearMap hf

/--
概要：基礎環上可算生成な代数上の有限加群は基礎環上可算生成。
方針：代数の可算生成集合と有限個の加群生成元の作用像を取り、線形包の二重の生成性を使う。
規約：KST §5、Stacks 05DP・059X、実際の両作用の塔を仮定する。
使われ方：有限型代数上の有限加群を基礎環上の可算生成加群と扱う。
-/
theorem hasCountableGeneratingSet_restrictScalars_of_finite
    (R B M : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (hB : HasCountableGeneratingSet R B) : HasCountableGeneratingSet R M := by
  classical
  obtain ⟨S, hSc, hS⟩ := hB
  let : Countable S := hSc.to_subtype
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := B) (M := M)
  let g : S × Fin n → M := fun x => x.1.val • v x.2
  let T := Submodule.span R (Set.range g)
  have hgen (b : B) (j : Fin n) : b • v j ∈ T := by
    let η : B →ₗ[R] M := (LinearMap.toSpanSingleton B M (v j)).restrictScalars R
    have hη : (Submodule.span R S).map η ≤ T := by
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨b, hb, rfl⟩
      exact Submodule.subset_span ⟨(⟨b, hb⟩, j), rfl⟩
    exact hη ⟨b, by rw [hS]; trivial, rfl⟩
  have hspan (x : M) (hx : x ∈ Submodule.span B (Set.range v)) :
      ∀ b : B, b • x ∈ T := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact fun b => hgen b j
    | zero => intro b; simpa only [smul_zero] using T.zero_mem
    | add x y _ _ hx hy =>
      intro b
      simpa only [smul_add] using T.add_mem (hx b) (hy b)
    | smul c x _ hx =>
      intro b
      simpa only [mul_smul] using hx (b * c)
  refine ⟨Set.range g, Set.countable_range g, top_unique ?_⟩
  intro x _
  have hx : x ∈ Submodule.span B (Set.range v) := by rw [hv]; trivial
  simpa only [one_smul] using hspan x hx 1

/--
概要：有限型代数上の有限加群は基礎環上可算生成。
方針：代数の単項式による可算生成性と有限加群の係数制限を合成する。
規約：KST §5、Stacks 05DP・059X、Noether 性・平坦性・幾何学的整性は不要。
使われ方：射影性の原典経路の可算生成性の仮定を実際に満たす。
-/
theorem hasCountableGeneratingSet_of_finiteType_finite
    (R B M : Type*) [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M] :
    HasCountableGeneratingSet R M :=
  hasCountableGeneratingSet_restrictScalars_of_finite R B M
    (hasCountableGeneratingSet_of_finiteType R B)

/--
概要：可算生成集合を持つ加群には自然数で添字付けた生成元列がある。
方針：生成集合に零を追加して非空にし、自然数による列挙を取る。
規約：KST §5、Stacks 05DP・059X、零加群と空の元の生成集合も許す。
使われ方：生成元を一つずつ追加する有限自由近似列の入力。
-/
theorem HasCountableGeneratingSet.exists_nat_spanning
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : HasCountableGeneratingSet R M) :
    ∃ g : ℕ → M, Submodule.span R (Set.range g) = ⊤ := by
  obtain ⟨S, hSc, hS⟩ := hM
  obtain ⟨g, hg⟩ := (hSc.insert 0).exists_eq_range (Set.insert_nonempty 0 S)
  refine ⟨g, ?_⟩
  rw [← hg, Submodule.span_insert_zero, hS]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
