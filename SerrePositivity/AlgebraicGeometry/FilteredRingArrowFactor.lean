module

public import SerrePositivity.AlgebraicGeometry.FilteredRingSameStageEquality

/-!
概要：filtered 余極限の間の射への有限表示な可換正方形を、同じ有限段へ因子化する。
方針：両辺を因子化して共通段へ移し、正方形の等式をさらに一つの後段で満たす。
規約：係数・両辺の元の射・正方形の可換性を同時に保持する。
使われ方：B03・B04 の旧被覆模型から新しい係数模型への射の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u

/-- 余極限の射への有限表示な正方形は、係数を保って同じ段へ因子化する。 -/
theorem exists_filtered_ring_arrow_factor
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (k : CommRingCat.{u}) (F G : J ⥤ CommRingCat.{u}) (τ : F ⟶ G)
    (α : (Functor.const J).obj k ⟶ F)
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (φ : cF.pt ⟶ cG.pt) (hφ : ∀ j, cF.ι.app j ≫ φ = τ.app j ≫ cG.ι.app j)
    {A D : CommRingCat.{u}} (fA : k ⟶ A) (fD : k ⟶ D)
    (hA : fA.hom.FinitePresentation) (hD : fD.hom.FinitePresentation)
    (t : A ⟶ D) (ht : fA ≫ t = fD)
    (a : A ⟶ cF.pt) (d : D ⟶ cG.pt)
    (ha : ∀ j, fA ≫ a = α.app j ≫ cF.ι.app j) (hsq : a ≫ φ = t ≫ d) :
    ∃ (j : J) (a₀ : A ⟶ F.obj j) (d₀ : D ⟶ G.obj j),
      fA ≫ a₀ = α.app j ∧ fD ≫ d₀ = α.app j ≫ τ.app j ∧
      a₀ ≫ cF.ι.app j = a ∧ d₀ ≫ cG.ι.app j = d ∧ a₀ ≫ τ.app j = t ≫ d₀ := by
  let γ : (Functor.const J).obj k ⟶ G := α ≫ τ
  have hd : ∀ j, fD ≫ d = γ.app j ≫ cG.ι.app j := by
    intro j
    calc
      fD ≫ d = (fA ≫ t) ≫ d := by rw [ht]
      _ = (fA ≫ a) ≫ φ := by rw [Category.assoc, ← hsq, Category.assoc]
      _ = (α.app j ≫ cF.ι.app j) ≫ φ := by rw [ha]
      _ = γ.app j ≫ cG.ι.app j := by rw [Category.assoc, hφ]; rfl
  obtain ⟨iA, a₁, ha₁, hea⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    k F α fA cF hcF hA a ha
  obtain ⟨iD, d₁, hd₁, hed⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    k G γ fD cG hcG hD d hd
  let i := IsFiltered.max iA iD
  let u : iA ⟶ i := IsFiltered.leftToMax iA iD
  let v : iD ⟶ i := IsFiltered.rightToMax iA iD
  let a₂ := a₁ ≫ F.map u
  let d₂ := d₁ ≫ G.map v
  have ha₂ : fA ≫ a₂ = α.app i := by
    dsimp only [a₂]
    rw [← Category.assoc, ha₁]
    exact (α.naturality u).symm.trans (Category.id_comp _)
  have hd₂ : fD ≫ d₂ = γ.app i := by
    dsimp only [d₂]
    rw [← Category.assoc, hd₁]
    exact (γ.naturality v).symm.trans (Category.id_comp _)
  have hea₂ : a₂ ≫ cF.ι.app i = a := by
    dsimp only [a₂]
    rw [Category.assoc, cF.w, ← hea]
  have hed₂ : d₂ ≫ cG.ι.app i = d := by
    dsimp only [d₂]
    rw [Category.assoc, cG.w, ← hed]
  have hleft : fA ≫ (a₂ ≫ τ.app i) = γ.app i := by
    rw [← Category.assoc, ha₂]
    rfl
  have hright : fA ≫ (t ≫ d₂) = γ.app i := by
    rw [← Category.assoc, ht, hd₂]
  have heq : (a₂ ≫ τ.app i) ≫ cG.ι.app i = (t ≫ d₂) ≫ cG.ι.app i := by
    calc
      (a₂ ≫ τ.app i) ≫ cG.ι.app i = (a₂ ≫ cF.ι.app i) ≫ φ := by
        rw [Category.assoc, ← hφ, ← Category.assoc]
      _ = a ≫ φ := by rw [hea₂]
      _ = t ≫ d := hsq
      _ = (t ≫ d₂) ≫ cG.ι.app i := by rw [Category.assoc, hed₂]
  obtain ⟨j, q, hq⟩ := exists_same_stage_ringHom_equality k G γ fA cG hcG
    (RingHom.FiniteType.of_finitePresentation hA) (a₂ ≫ τ.app i) (t ≫ d₂) hleft hright heq
  refine ⟨j, a₂ ≫ F.map q, d₂ ≫ G.map q, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ha₂]
    exact (α.naturality q).symm.trans (Category.id_comp _)
  · rw [← Category.assoc, hd₂]
    exact (γ.naturality q).symm.trans (Category.id_comp _)
  · rw [Category.assoc, cF.w, hea₂]
  · rw [Category.assoc, cG.w, hed₂]
  · calc
      (a₂ ≫ F.map q) ≫ τ.app j = (a₂ ≫ τ.app i) ≫ G.map q := by
        rw [Category.assoc, τ.naturality q, ← Category.assoc]
      _ = (t ≫ d₂) ≫ G.map q := hq
      _ = t ≫ (d₂ ≫ G.map q) := Category.assoc _ _ _

end SerrePositivity.AlgebraicGeometry
