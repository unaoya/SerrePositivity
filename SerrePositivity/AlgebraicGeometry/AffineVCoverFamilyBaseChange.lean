module

public import SerrePositivity.AlgebraicGeometry.AffineVCoverFamily
public import SerrePositivity.AlgebraicGeometry.AffineVCoverBaseChange

/-!
概要：有限族の付値判定は、各成分の実際の pushout による底変換で保たれる。
方針：付値環を持ち上げた一つの成分について、pushout の普遍性で写像を延長する。
規約：基底変更の平坦性を仮定せず、同じ成分と付値環拡大を使う。
使われ方：2g の v 被覆の細分と合成からの消去に必要な普遍性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A C : Type u} [CommRing A] [CommRing C]
variable {ι : Type u} [Finite ι]
variable (B D : ι → Type u) [∀ i, CommRing (B i)] [∀ i, CommRing (D i)]
variable (f : ∀ i, A →+* B i) (α : A →+* C)
variable (g : ∀ i, B i →+* D i) (β : ∀ i, C →+* D i)

/-- 各成分の pushout による、有限な affine v 被覆族の底変換。 -/
theorem IsAffineVCoverFamily.baseChange
    (H : ∀ i, IsPushout (CommRingCat.ofHom (f i)) (CommRingCat.ofHom α)
      (CommRingCat.ofHom (g i)) (CommRingCat.ofHom (β i)))
    (hf : IsAffineVCoverFamily B f) : IsAffineVCoverFamily D β := by
  intro V _ _ _ k
  obtain ⟨i, W, hW, hval, _, e, l, he, hl⟩ := hf V trivial (k.comp α)
  have h : CommRingCat.ofHom (f i) ≫ CommRingCat.ofHom l =
      CommRingCat.ofHom α ≫ CommRingCat.ofHom (e.comp k) := by
    apply CommRingCat.hom_ext
    exact hl
  let m := (H i).desc (CommRingCat.ofHom l) (CommRingCat.ofHom (e.comp k)) h
  refine ⟨i, W, hW, hval, trivial, e, m.hom, he, ?_⟩
  exact congrArg (fun q ↦ q.hom) ((H i).inr_desc _ _ h)

/-- 一点族の判定は一射の判定と同じ。 -/
theorem isAffineVCoverFamily_punit_iff {E : Type u} [CommRing E] (h : A →+* E) :
    IsAffineVCoverFamily (fun _ : PUnit.{u + 1} ↦ E) (fun _ ↦ h) ↔ IsAffineVCover h := by
  constructor
  · intro hf V _ _ k
    obtain ⟨_, W, hW, hval, _, e, l, he, hl⟩ := hf V trivial k
    exact ⟨W, hW, hval, e, l, he, hl⟩
  · intro hf
    exact isAffineVCoverFamily_of_member _ _ PUnit.unit hf

end SerrePositivity.AlgebraicGeometry
