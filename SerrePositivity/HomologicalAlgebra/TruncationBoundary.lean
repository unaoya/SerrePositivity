module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Single

/-! # 零ホモトピーを切り詰めたときの境界項

複体を下端 `a` で項ごとに切ると、零ホモトピーの等式には下端で誤差が残る。
その誤差は、切り捨てた `a-1` 次の項を `a` 次に置いた一項複体を経由する。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace SerrePositivity.TruncationBoundary

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

section linear

variable {R : Type*} [Semiring R] [Linear R C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') [e.IsRelIff]

instance restriction_linear : (e.restrictionFunctor C).Linear R where
  map_smul := by intros; rfl

instance extend_linear : (e.extendFunctor C).Linear R where
  map_smul r f := by
    ext i'
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      simp only [ComplexShape.Embedding.extendFunctor_map, extendMap_f _ _ hi,
        smul_f_apply, Linear.comp_smul, Linear.smul_comp]
    · apply (isZero_extend_X _ e i' (fun i h ↦ hi ⟨i, h⟩)).eq_of_src

lemma stupidTruncMap_smul_id (K : HomologicalComplex C c') (r : R) :
    stupidTruncMap (r • 𝟙 K) e = r • 𝟙 (K.stupidTrunc e) := by
  change (e.extendFunctor C).map ((e.restrictionFunctor C).map (r • 𝟙 K)) = _
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

end linear

/-- 下端の直前の項を、切り詰めの下端に置く。 -/
noncomputable def boundary (K : CochainComplex C ℤ) (a : ℤ) : CochainComplex C ℤ :=
  ((CochainComplex.single₀ C).obj
    (K.X ((ComplexShape.embeddingUpIntGE a).f 0 - 1))).extend
    (ComplexShape.embeddingUpIntGE a)

/-- 境界複体は切り詰めの下端以外で零。 -/
lemma boundary_isZero_X (K : CochainComplex C ℤ) (a q : ℤ) (hq : q ≠ a) :
    IsZero ((boundary K a).X q) := by
  let e := ComplexShape.embeddingUpIntGE a
  by_cases hq' : ∃ n, e.f n = q
  · obtain ⟨n, hn⟩ := hq'
    have hn' : n ≠ 0 := by
      intro h
      subst n
      exact hq (by simpa [e] using hn.symm)
    exact (isZero_single_obj_X (ComplexShape.up ℕ) 0 _ n hn').of_iso
      (((CochainComplex.single₀ C).obj (K.X (e.f 0 - 1))).extendXIso e hn)
  · exact isZero_extend_X _ e q (fun n hn ↦ hq' ⟨n, hn⟩)

/-- 下端における境界複体の項は、切り捨てた直前の項である。 -/
noncomputable def boundaryXIso (K : CochainComplex C ℤ) (a : ℤ) :
    (boundary K a).X a ≅ K.X (a - 1) :=
  (((CochainComplex.single₀ C).obj
    (K.X ((ComplexShape.embeddingUpIntGE a).f 0 - 1))).extendXIso
      (ComplexShape.embeddingUpIntGE a) (i := 0) (by simp)) ≪≫
    eqToIso (by simp)

/-- 自然数添字への制限で生じる境界項を経由する因子分解。 -/
lemma restriction_factorization (K : CochainComplex C ℤ) (a : ℤ)
    (f : K ⟶ K) (h : Homotopy f 0) :
    ∃ (u : K.restriction (ComplexShape.embeddingUpIntGE a) ⟶
        (CochainComplex.single₀ C).obj
          (K.X ((ComplexShape.embeddingUpIntGE a).f 0 - 1)))
      (v : (CochainComplex.single₀ C).obj
          (K.X ((ComplexShape.embeddingUpIntGE a).f 0 - 1)) ⟶
        K.restriction (ComplexShape.embeddingUpIntGE a)),
      Nonempty (Homotopy (restrictionMap f (ComplexShape.embeddingUpIntGE a)) (u ≫ v)) := by
  let e := ComplexShape.embeddingUpIntGE a
  let L := K.restriction e
  let V := K.X (e.f 0 - 1)
  let u₀ : L.X 0 ⟶ V := h.hom (e.f 0) (e.f 0 - 1)
  let v₀ : V ⟶ L.X 0 := K.d (e.f 0 - 1) (e.f 0)
  have hv : v₀ ≫ L.d 0 1 = 0 := K.d_comp_d _ _ _
  let u := (CochainComplex.toSingle₀Equiv L V).symm u₀
  let v := (CochainComplex.fromSingle₀Equiv L V).symm ⟨v₀, hv⟩
  refine ⟨u, v, ⟨{ hom := fun i j ↦ h.hom (e.f i) (e.f j), zero := ?_, comm := ?_ }⟩⟩
  · intro i j hij
    exact h.zero _ _ (by rwa [e.rel_iff])
  · intro n
    cases n with
    | zero =>
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel 0 1 by simp),
        prevD_eq_zero _ 0 (by simp), add_zero, comp_f]
      simp only [u, v, CochainComplex.toSingle₀Equiv_symm_apply_f_zero,
        CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
      have hc := h.comm (e.f 0)
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (e.f 0) (e.f 1) by simp [e]),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (e.f 0 - 1) (e.f 0) by simp),
        zero_f, add_zero] at hc
      exact hc
    | succ n =>
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) by simp),
        prevD_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) by simp), comp_f]
      simp only [u, CochainComplex.toSingle₀Equiv_symm_apply_f_succ, zero_comp, add_zero]
      have hc := h.comm (e.f (n + 1))
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (e.f (n + 1)) (e.f (n + 2)) by simp [e]; omega),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (e.f n) (e.f (n + 1)) by simp [e]; omega),
        zero_f, add_zero] at hc
      exact hc

/-- 項ごとの切り詰めに誘導される射は、一項複体を経由する射とホモトピック。 -/
lemma factorization (K : CochainComplex C ℤ) (a : ℤ) (f : K ⟶ K) (h : Homotopy f 0) :
    ∃ (u : K.stupidTrunc (ComplexShape.embeddingUpIntGE a) ⟶ boundary K a)
      (v : boundary K a ⟶ K.stupidTrunc (ComplexShape.embeddingUpIntGE a)),
      Nonempty (Homotopy (stupidTruncMap f (ComplexShape.embeddingUpIntGE a)) (u ≫ v)) := by
  obtain ⟨u, v, ⟨H⟩⟩ := restriction_factorization K a f h
  refine ⟨extendMap u _, extendMap v _, ?_⟩
  have he := H.extend (ComplexShape.embeddingUpIntGE a)
  simpa only [extendMap_comp, stupidTruncMap] using (Nonempty.intro he)

/-- 零ホモトピックなスカラー作用の切り詰めは、境界の一項複体を経由する。 -/
lemma scalar_factorization {R : Type*} [Semiring R] [Linear R C]
    (K : CochainComplex C ℤ) (a : ℤ) (r : R) (h : Homotopy (r • 𝟙 K) 0) :
    ∃ (u : K.stupidTrunc (ComplexShape.embeddingUpIntGE a) ⟶ boundary K a)
      (v : boundary K a ⟶ K.stupidTrunc (ComplexShape.embeddingUpIntGE a)),
      Nonempty (Homotopy (r • 𝟙 _) (u ≫ v)) := by
  simpa only [stupidTruncMap_smul_id] using factorization K a (r • 𝟙 K) h

end SerrePositivity.TruncationBoundary
