module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
概要：有限個の固有な周辺を持つ支配射を、実際の直和にまとめる。
方針：固有な二項直和からの射と、開包含の二項直和を有限回組み立てる。
規約：空の族も含め、各成分の元の対象への可換式を保つ。
使われ方：C06 の既約成分の有限族から一般の対象への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 二つの固有射の直和からの射は固有。 -/
theorem isProper_coprod_desc {A B X : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) [IsProper f] [IsProper g] :
    IsProper (coprod.desc f g) := by
  haveI : IsProper (coprod.map f g) :=
    IsZariskiLocalAtTarget.coprodMap f g inferInstance inferInstance
  have h : coprod.map f g ≫ coprod.desc (𝟙 X) (𝟙 X) = coprod.desc f g := by
    apply coprod.hom_ext <;> simp
  rw [← h]
  infer_instance

/-- 有限個の固有な周辺を持つ支配射を、一つの実際の支配射にまとめる。 -/
theorem exists_finite_proper_domination_union {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℕ) (T P : Fin n → Scheme.{u}) (h : ∀ i, T i ⟶ X)
    (t : ∀ i, T i ⟶ P i) (q : ∀ i, P i ⟶ S)
    (hh : ∀ i, IsProper (h i)) (ht : ∀ i, IsOpenImmersion (t i))
    (hq : ∀ i, IsProper (q i)) (hcomm : ∀ i, t i ≫ q i = h i ≫ f) :
    ∃ (T' P' : Scheme.{u}) (h' : T' ⟶ X) (t' : T' ⟶ P') (q' : P' ⟶ S)
      (l : ∀ i, T i ⟶ T'),
      IsProper h' ∧ IsOpenImmersion t' ∧ IsProper q' ∧
      t' ≫ q' = h' ≫ f ∧ ∀ i, l i ≫ h' = h i := by
  induction n with
  | zero =>
      refine ⟨⊥_ Scheme, ⊥_ Scheme, initial.to X, 𝟙 _, initial.to S,
        (fun i ↦ Fin.elim0 i), inferInstance, inferInstance, inferInstance, ?_,
        (fun i ↦ Fin.elim0 i)⟩
      apply initial.hom_ext
  | succ n ih =>
      obtain ⟨T', P', h', t', q', l', hh', ht', hq', hcomm', hl'⟩ :=
        ih (fun i ↦ T i.succ) (fun i ↦ P i.succ) (fun i ↦ h i.succ)
          (fun i ↦ t i.succ) (fun i ↦ q i.succ) (fun i ↦ hh i.succ)
          (fun i ↦ ht i.succ) (fun i ↦ hq i.succ) (fun i ↦ hcomm i.succ)
      let H := coprod.desc (h 0) h'
      let E := coprod.map (t 0) t'
      let Q := coprod.desc (q 0) q'
      let L : ∀ i : Fin (n + 1), T i ⟶ T 0 ⨿ T' :=
        Fin.cases coprod.inl (fun i ↦ l' i ≫ coprod.inr)
      letI : IsProper (h 0) := hh 0
      letI : IsProper h' := hh'
      letI : IsProper (q 0) := hq 0
      letI : IsProper q' := hq'
      have hH : IsProper H := isProper_coprod_desc (h 0) h'
      have hQ : IsProper Q := isProper_coprod_desc (q 0) q'
      have hE : IsOpenImmersion E := IsZariskiLocalAtTarget.coprodMap (t 0) t' (ht 0) ht'
      refine ⟨T 0 ⨿ T', P 0 ⨿ P', H, E, Q, L, hH, hE, hQ, ?_, ?_⟩
      · apply coprod.hom_ext <;> simp [E, Q, H, Category.assoc, hcomm 0, hcomm']
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [L, H]
        · simp [L, H, Category.assoc, hl']

end SerrePositivity.AlgebraicGeometry
