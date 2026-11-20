module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeCountableGeneration
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：KST §5、Stacks 05DP・059X の Noether 基底での可算生成部分加群の構成。
方針：可算な有限生成部分加群族で覆い、各有限生成集合の和集合を取る。
規約：基礎環の可算性は要求せず、生成集合の可算性を扱う。
使われ方：有限型加群の可算個の関係式を構成する準備。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：可算な有限生成部分加群族が全体を覆えば、その加群は可算生成。
方針：各有限生成集合を選び、その可算和集合の線形包を計算する。
規約：KST §5、Stacks 05DP・059X、基礎環の Noether 性はこの補題には不要。
使われ方：有限個の元で生成される部分ごとの Noether 性から可算生成性を得る。
-/
theorem hasCountableGeneratingSet_of_iSup_fg
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Countable ι]
    (N : ι → Submodule R M) (hfg : ∀ i, (N i).FG) (hcover : (⨆ i, N i) = ⊤) :
    HasCountableGeneratingSet R M := by
  classical
  choose S hS using hfg
  refine ⟨⋃ i, (S i : Set M), Set.countable_iUnion (fun i => (S i).finite_toSet.countable), ?_⟩
  rw [Submodule.span_iUnion]
  simp_rw [hS]
  exact hcover

/--
概要：Noether 基礎環上の可算生成加群の任意の部分加群は可算生成。
方針：可算生成集合の有限部分集合の線形包との交わりを、可算な有限生成被覆として使う。
規約：KST §5、Stacks 05DP・059X、部分加群は有限生成とは限らない。
使われ方：可算自由加群からの表示の核に可算個の関係式を取る。
-/
theorem HasCountableGeneratingSet.submodule
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    (hM : HasCountableGeneratingSet R M) (N : Submodule R M) :
    HasCountableGeneratingSet R N := by
  classical
  obtain ⟨S, hSc, hS⟩ := hM
  let : Countable S := hSc.to_subtype
  let T (t : Finset S) : Submodule R M := Submodule.span R (Subtype.val '' (t : Set S))
  let L (t : Finset S) : Submodule R N := (T t).comap N.subtype
  have hTfg (t : Finset S) : (T t).FG :=
    Submodule.fg_span (t.finite_toSet.image Subtype.val)
  have hLfg (t : Finset S) : (L t).FG := by
    apply Submodule.fg_of_fg_map_injective N.subtype Subtype.val_injective
    rw [Submodule.map_comap_eq, N.range_subtype]
    exact (hTfg t).of_le inf_le_right
  apply hasCountableGeneratingSet_of_iSup_fg L hLfg
  apply top_unique
  intro x _
  have hx : x.val ∈ Submodule.span R S := by rw [hS]; trivial
  obtain ⟨t, htS, hxt⟩ := Submodule.mem_span_finite_of_mem_span hx
  let t' : Finset S := t.subtype (· ∈ S)
  have himage : Subtype.val '' (t' : Set S) = (t : Set M) := by
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Finset.mem_subtype.mp hy
    · intro hy
      exact ⟨⟨y, htS hy⟩, Finset.mem_subtype.mpr hy, rfl⟩
  apply (le_iSup L t')
  change x.val ∈ Submodule.span R (Subtype.val '' (t' : Set S))
  rw [himage]
  exact hxt

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
