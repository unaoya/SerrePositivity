module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
概要：任意の階数の付値環で試す affine v 被覆の入口。
方針：BS17 Definition 2.1 の持ち上げを、忠実平坦な付値環拡大と環準同型で保持する。
規約：試験環と拡大環は同じ宇宙。零環を入力から除外しない。
使われ方：2g の有限族と一射の橋、Rydh の細分の入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u

/-- BS17 Definition 2.1 の一射の affine v 被覆。W の整域構造を同じ証人に保持する。 -/
def IsAffineVCover {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V] (k : A →+* V),
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ ∃ (e : V →+* W) (l : B →+* W),
        e.FaithfullyFlat ∧ l.comp f = e.comp k

/-- 階数条件を指定した付値判定。有限族の drafts の述語と同じ量化を使う。 -/
def ValuativeCoverFamily (rank : CommRingCat.{u} → Prop)
    {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V], rank V → ∀ k : A →+* V,
    ∃ (i : ι) (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ rank W ∧ ∃ (e : V →+* W) (l : B i →+* W),
        e.FaithfullyFlat ∧ l.comp (f i) = e.comp k

/-- BS17 Definition 2.1 の有限族の affine v 被覆。付値環の階数は制限しない。 -/
def IsAffineVCoverFamily {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun _ => True) B f

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- 切断を持つ環準同型は affine v 被覆。 -/
theorem isAffineVCover_of_retraction (f : A →+* B) (r : B →+* A)
    (hr : r.comp f = RingHom.id A) : IsAffineVCover f := by
  intro V _ _ k
  refine ⟨V, inferInstance, inferInstance, RingHom.id V, k.comp r,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id, ?_⟩
  rw [RingHom.comp_assoc, hr, RingHom.comp_id, RingHom.id_comp]

/-- 恒等写像は affine v 被覆。 -/
theorem isAffineVCover_id : IsAffineVCover (RingHom.id A) :=
  isAffineVCover_of_retraction _ (RingHom.id A) (RingHom.id_comp _)

/-- affine v 被覆の合成も同じ付値判定を満たす。 -/
theorem IsAffineVCover.comp {f : A →+* B} {g : B →+* C}
    (hg : IsAffineVCover g) (hf : IsAffineVCover f) : IsAffineVCover (g.comp f) := by
  intro V _ _ k
  obtain ⟨W, hW, hvalW, e, l, he, hl⟩ := hf V k
  letI : IsDomain W := hW
  letI : ValuationRing W := hvalW
  obtain ⟨Z, hZ, hvalZ, d, m, hd, hm⟩ := hg W l
  refine ⟨Z, hZ, hvalZ, d.comp e, m,
    RingHom.FaithfullyFlat.stableUnderComposition e d he hd, ?_⟩
  rw [← RingHom.comp_assoc, hm, RingHom.comp_assoc, hl, RingHom.comp_assoc]

/-- v 被覆の細分から元の射の付値判定を得る。 -/
theorem IsAffineVCover.of_comp {f : A →+* B} {g : B →+* C}
    (h : IsAffineVCover (g.comp f)) : IsAffineVCover f := by
  intro V _ _ k
  obtain ⟨W, hW, hvalW, e, l, he, hl⟩ := h V k
  exact ⟨W, hW, hvalW, e, l.comp g, he, by rwa [RingHom.comp_assoc]⟩

end SerrePositivity.AlgebraicGeometry
