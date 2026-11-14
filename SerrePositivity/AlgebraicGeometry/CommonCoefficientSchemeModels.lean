module

public import SerrePositivity.AlgebraicGeometry.SchemeFinitePresentationCoefficientModel

/-!
概要：有限個の実際のスキーム模型を、一つの有限生成係数部分代数へ移す。
方針：有限生成元の有限和集合を取り、各模型を実際に底変換する。
規約：両方の Cartesian 比較と元の比較射の可換式を保つ。
使われ方：B02 の有限個の細分の対象と射を同じ係数段へそろえる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v w

/-- 有限個の有限生成係数部分代数を含む、有限生成係数部分代数を取れる。 -/
theorem exists_common_finitelyGenerated_coefficient_extension
    (k : Type v) (R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {I : Type w} [Finite I] (A : I → Subalgebra k R) (hA : ∀ i, (A i).FG) :
    ∃ B : Subalgebra k R, B.FG ∧ ∀ i, A i ≤ B := by
  classical
  choose s hs using hA
  let c : Set R := ⋃ i, (s i : Set R)
  let B := Algebra.adjoin k c
  have hc : c.Finite := Set.finite_iUnion (fun i ↦ (s i).finite_toSet)
  refine ⟨B, Subalgebra.fg_def.mpr ⟨c, hc, rfl⟩, ?_⟩
  intro i
  rw [← hs i]
  exact Algebra.adjoin_mono (Set.subset_iUnion (fun i ↦ (s i : Set R)) i)

/-- 有限個の実際の模型を、一つの共通係数段の実際の底変換模型へそろえる。 -/
theorem exists_common_coefficient_scheme_models
    (k : Type v) (R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {I : Type w} [Finite I] (A : I → Subalgebra k R) (hA : ∀ i, (A i).FG)
    (X Y : I → Scheme.{u}) (f : ∀ i, X i ⟶ Spec (CommRingCat.of R))
    (p : ∀ i, Y i ⟶ Spec (CommRingCat.of (A i))) (a : ∀ i, X i ⟶ Y i)
    (hpb : ∀ i, IsPullback (a i) (f i) (p i)
      (Spec.map (CommRingCat.ofHom (algebraMap (A i) R)))) :
    ∃ B : Subalgebra k R, B.FG ∧
      ∃ γ : ∀ i, Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (A i)),
        (∀ i, Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ γ i =
          Spec.map (CommRingCat.ofHom (algebraMap (A i) R))) ∧
        ∀ i, ∃ (Y' : Scheme.{u}) (p' : Y' ⟶ Spec (CommRingCat.of B))
          (b : Y' ⟶ Y i) (a' : X i ⟶ Y'),
          IsPullback b p' (p i) (γ i) ∧
          IsPullback a' (f i) p' (Spec.map (CommRingCat.ofHom (algebraMap B R))) ∧
          a' ≫ b = a i := by
  obtain ⟨B, hB, hAB⟩ := exists_common_finitelyGenerated_coefficient_extension k R A hA
  let δ := Spec.map (CommRingCat.ofHom (algebraMap B R))
  let γ (i : I) := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hAB i)).toRingHom)
  have hδ (i : I) : δ ≫ γ i = Spec.map (CommRingCat.ofHom (algebraMap (A i) R)) := by
    dsimp [δ, γ]
    rw [← Spec.map_comp]
    congr 1
  refine ⟨B, hB, γ, hδ, ?_⟩
  intro i
  let Y' := pullback (p i) (γ i)
  let p' : Y' ⟶ Spec (CommRingCat.of B) := pullback.snd (p i) (γ i)
  let b : Y' ⟶ Y i := pullback.fst (p i) (γ i)
  let a' : X i ⟶ Y' := pullback.lift (a i) (f i ≫ δ) (by
    rw [Category.assoc, hδ]
    exact (hpb i).w)
  have hpb' : IsPullback a' (f i) p' δ := by
    apply IsPullback.of_right ?_ (by simp [a', p']) (IsPullback.of_hasPullback (p i) (γ i))
    simpa only [a', pullback.lift_fst, hδ] using hpb i
  exact ⟨Y', p', b, a', IsPullback.of_hasPullback (p i) (γ i), hpb', pullback.lift_fst _ _ _⟩

end SerrePositivity.AlgebraicGeometry
