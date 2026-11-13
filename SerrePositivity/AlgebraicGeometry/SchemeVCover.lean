module

public import SerrePositivity.AlgebraicGeometry.AffineVCover
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
概要：付値環の拡大で試すスキームの v 被覆と affine 版の橋。
方針：Spec の完全忠実性を使って、同じ可換式を環の射とスキームの射で読む。
規約：始域・終域の affine 性は定義に課さず、宇宙は試験付値環とそろえる。
使われ方：Rydh 3.10 の固有因子と affine な入力をつなぐ G0 の入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u

/-- BS17 Definition 2.1 のスキームの付値持ち上げ。付値環拡大は忠実平坦とする。 -/
def IsSchemeVCover {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V] (k : Spec V ⟶ Y),
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ ∃ (e : V →+* W) (l : Spec W ⟶ X),
        e.FaithfullyFlat ∧ l ≫ f = Spec.map (CommRingCat.ofHom e) ≫ k

/-- affine スキームの付値判定は、同じ環の準同型の付値判定と同値。 -/
theorem isSchemeVCover_specMap_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    IsSchemeVCover (Spec.map (CommRingCat.ofHom f)) ↔ IsAffineVCover f := by
  constructor
  · intro h V _ _ k
    obtain ⟨W, hW, hval, e, l, he, hl⟩ := h V (Spec.map (CommRingCat.ofHom k))
    obtain ⟨m, rfl⟩ := Spec.map_surjective l
    refine ⟨W, hW, hval, e, m.hom, he, ?_⟩
    have hr : CommRingCat.ofHom f ≫ m =
        CommRingCat.ofHom k ≫ CommRingCat.ofHom e := by
      apply Spec.map_injective
      simpa only [Spec.map_comp] using hl
    exact congrArg (fun q ↦ q.hom) hr
  · intro h V _ _ k
    obtain ⟨m, rfl⟩ := Spec.map_surjective k
    obtain ⟨W, hW, hval, e, l, he, hl⟩ := h V m.hom
    refine ⟨W, hW, hval, e, Spec.map (CommRingCat.ofHom l), he, ?_⟩
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q)) hl

end SerrePositivity.AlgebraicGeometry
