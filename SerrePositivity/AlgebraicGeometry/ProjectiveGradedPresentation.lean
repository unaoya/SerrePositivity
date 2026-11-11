module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：有限生成の次数付き加群の斉次生成元と、次数成分の完全性。
方針：既存の生成元を直和分解し、次数を保つ写像と各成分の射影を比較する。
規約：次数の集合は任意。斉次な分解を与えることを仮定する。
使われ方：射影 Čech コホモロジーを有限斉次自由表示で計算する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum BigOperators

variable {R S M N P : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
variable {ι : Type*} [DecidableEq ι]

/--
概要：有限生成の次数付き加群は、有限個の斉次元で生成される。
方針：有限生成元それぞれの有限台を取り、その斉次成分をまとめる。
規約：生成には S の作用を使い、次数成分は R 部分加群で与える。
使われ方：射影有限性で有限個の多項式環の捻りから全射を作る。
-/
theorem exists_finset_homogeneous_span_top (G : ι → Submodule R M)
    [DirectSum.Decomposition G] [Module.Finite S M] :
    ∃ t : Finset M, (∀ x ∈ t, ∃ i, x ∈ G i) ∧ Submodule.span S (↑t : Set M) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := S) (M := M))
  let t := s.biUnion fun x ↦ (DirectSum.decompose G x).support.image
    (fun i ↦ ((DirectSum.decompose G x i : G i) : M))
  refine ⟨t, ?_, top_unique ?_⟩
  · intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i, (DirectSum.decompose G y i).property⟩
  · rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← DirectSum.sum_support_decompose G x]
    exact Submodule.sum_mem _ fun i hi ↦ Submodule.subset_span
      (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)

/-- 次数を保つ写像は、斉次成分を取る射影と可換になる。 -/
theorem projectiveGradedMap_decompose (G : ι → Submodule R M) (H : ι → Submodule R N)
    [DirectSum.Decomposition G] [DirectSum.Decomposition H] (f : M →ₗ[S] N)
    (hf : ∀ i, ∀ x ∈ G i, f x ∈ H i) (x : M) (i : ι) :
    f (DirectSum.decompose G x i : M) = (DirectSum.decompose H (f x) i : N) := by
  classical
  let s := insert i (DirectSum.decompose G x).support
  have hx : ∑ j ∈ s, (DirectSum.decompose G x j : M) = x := by
    by_cases hi : i ∈ (DirectSum.decompose G x).support
    · simpa only [s, Finset.insert_eq_of_mem hi] using DirectSum.sum_support_decompose G x
    · have hz : DirectSum.decompose G x i = 0 := DFinsupp.notMem_support_iff.mp hi
      rw [show s = insert i (DirectSum.decompose G x).support from rfl, Finset.sum_insert hi,
        hz, Submodule.coe_zero, zero_add, DirectSum.sum_support_decompose]
  have hfx : f x = ∑ j ∈ s, f (DirectSum.decompose G x j : M) := by
    rw [← map_sum, hx]
  conv_rhs => rw [hfx]
  rw [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_insert_self _ _)]
  · exact (DirectSum.decompose_of_mem_same H (hf i _ (DirectSum.decompose G x i).property)).symm
  · intro j _ hj
    exact DirectSum.decompose_of_mem_ne H (hf j _ (DirectSum.decompose G x j).property) hj

/-- 次数を保つ完全列は、各次数の斉次成分でも完全。 -/
theorem projectiveGradedMap_exact_piece (G : ι → Submodule R M) (H : ι → Submodule R N)
    [DirectSum.Decomposition G] [DirectSum.Decomposition H]
    (f : M →ₗ[S] N) (g : N →ₗ[S] P) (hf : ∀ i, ∀ x ∈ G i, f x ∈ H i)
    (he : Function.Exact f g) (i : ι) (y : H i) :
    g y.val = 0 ↔ ∃ x : G i, f x.val = y.val := by
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (he y.val).mp hy
    refine ⟨DirectSum.decompose G x i, ?_⟩
    rw [projectiveGradedMap_decompose G H f hf, hx, DirectSum.decompose_of_mem_same H y.property]
  · rintro ⟨x, hx⟩
    exact (he y.val).mpr ⟨x.val, hx⟩

/-- 全射な次数付き写像は各次数成分でも全射。 -/
theorem projectiveGradedMap_surjective_piece (G : ι → Submodule R M) (H : ι → Submodule R N)
    [DirectSum.Decomposition G] [DirectSum.Decomposition H] (f : M →ₗ[S] N)
    (hf : ∀ i, ∀ x ∈ G i, f x ∈ H i) (hs : Function.Surjective f)
    (i : ι) (y : H i) : ∃ x : G i, f x.val = y.val := by
  obtain ⟨x, hx⟩ := hs y.val
  refine ⟨DirectSum.decompose G x i, ?_⟩
  rw [projectiveGradedMap_decompose G H f hf, hx, DirectSum.decompose_of_mem_same H y.property]

/-- 次数を保つ写像の核の、元の加群の次数成分との交わり。 -/
def projectiveGradedKernelPiece (G : ι → Submodule R M) (f : M →ₗ[S] N) (i : ι) :
    Submodule R (LinearMap.ker f) :=
  (G i).comap ((LinearMap.ker f).subtype.restrictScalars R)

/-- 次数を保つ写像の核は、元の加群の次数分解を受け継ぐ。 -/
@[instance_reducible]
def projectiveGradedKernelDecomposition (G : ι → Submodule R M) (H : ι → Submodule R N)
    [DirectSum.Decomposition G] [DirectSum.Decomposition H] (f : M →ₗ[S] N)
    (hf : ∀ i, ∀ x ∈ G i, f x ∈ H i) :
    DirectSum.Decomposition (projectiveGradedKernelPiece G f) := by
  classical
  let K := LinearMap.ker f
  let P := projectiveGradedKernelPiece G f
  let i : K →+ M := (LinearMap.ker f).subtype.toAddMonoidHom
  let j (d : ι) : P d →+ G d :=
    { toFun := fun x ↦ ⟨x.val.val, x.property⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hj : Function.Injective (DirectSum.map j) := (DirectSum.map_injective j).mpr
    (fun d x y h ↦ Subtype.ext (Subtype.ext (congrArg (fun z : G d ↦ z.val) h)))
  have hsum (a : ⨁ d, P d) :
      i (DirectSum.coeAddMonoidHom P a) = DirectSum.coeAddMonoidHom G (DirectSum.map j a) := by
    have hm : i.comp (DirectSum.coeAddMonoidHom P) =
        (DirectSum.coeAddMonoidHom G).comp (DirectSum.map j) := by
      ext d x
      simp [j, i]
    exact DFunLike.congr_fun hm a
  let lift (x : K) (d : ι) : P d :=
    ⟨⟨(DirectSum.decompose G x.val d).val, by
      change f (DirectSum.decompose G x.val d).val = 0
      rw [projectiveGradedMap_decompose G H f hf, show f x.val = 0 from x.property]
      simp⟩, (DirectSum.decompose G x.val d).property⟩
  let decompose (x : K) : ⨁ d, P d :=
    DFinsupp.mk (DirectSum.decompose G x.val).support (fun d ↦ lift x d.val)
  have hdecompose (x : K) : DirectSum.map j (decompose x) = DirectSum.decompose G x.val := by
    ext d
    by_cases hd : d ∈ (DirectSum.decompose G x.val).support
    · simp [decompose, DFinsupp.mk_of_mem hd, lift, j]
    · have hz := DFinsupp.notMem_support_iff.mp hd
      simp [decompose, DFinsupp.mk_of_notMem hd, hz]
  refine { decompose' := decompose, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply Subtype.ext
    change i (DirectSum.coeAddMonoidHom P (decompose x)) = x.val
    rw [hsum, hdecompose]
    exact (DirectSum.decompose G).left_inv x.val
  · intro a
    apply hj
    rw [hdecompose, show (DirectSum.coeAddMonoidHom P a : K).val =
      i (DirectSum.coeAddMonoidHom P a) from rfl, hsum]
    exact (DirectSum.decompose G).right_inv (DirectSum.map j a)

end SerrePositivity.AlgebraicGeometry
