module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
概要：二つの因子の開被覆による Cartesian 四角形の貼り合わせの法則。
方針：既存の開被覆による判定を二回使い、同じ像の開埋め込みを同定する。
規約：元の実際の射と局所四角形を使う。
使われ方：Segre の標準開の Cartesian 四角形を大域へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v w

/-- 二つの開を順に引き戻した開埋め込みの像は、二つの逆像の交叉。 -/
theorem opensRange_iteratedPullbackFst
    {W X Y U V : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    (pullback.fst (pullback.fst f i ≫ g) j ≫ pullback.fst f i).opensRange =
      (f ⁻¹ᵁ i.opensRange) ⊓ (g ⁻¹ᵁ j.opensRange) := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_pullbackFst,
    Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.opensRange_pullbackFst]

set_option backward.isDefEq.respectTransparency false in
/-- 二つの因子の被覆上の同じ逆像の交叉で Cartesian なら、大域でも Cartesian。 -/
theorem isPullback_of_pairOpenCover
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z)
    (𝒰 : X.OpenCover.{v}) (𝒱 : Y.OpenCover.{w})
    (T : 𝒰.I₀ → 𝒱.I₀ → Scheme.{u})
    (e : ∀ i j, T i j ⟶ W) [∀ i j, IsOpenImmersion (e i j)]
    (a : ∀ i j, T i j ⟶ 𝒰.X i) (b : ∀ i j, T i j ⟶ 𝒱.X j)
    (ha : ∀ i j, e i j ≫ f = a i j ≫ 𝒰.f i)
    (hb : ∀ i j, e i j ≫ g = b i j ≫ 𝒱.f j)
    (hrange : ∀ i j, (e i j).opensRange =
      (f ⁻¹ᵁ (𝒰.f i).opensRange) ⊓ (g ⁻¹ᵁ (𝒱.f j).opensRange))
    (H : ∀ i j, IsPullback (a i j) (b i j) (𝒰.f i ≫ h) (𝒱.f j ≫ k)) :
    IsPullback f g h k := by
  apply Scheme.isPullback_of_openCover f g h k 𝒰
  intro i
  apply IsPullback.flip
  apply Scheme.isPullback_of_openCover _ _ _ _ 𝒱
  intro j
  let p := pullback.fst f (𝒰.f i)
  let q := pullback.snd f (𝒰.f i)
  let r := pullback.fst (p ≫ g) (𝒱.f j)
  let s := pullback.snd (p ≫ g) (𝒱.f j)
  change IsPullback s (r ≫ q) (𝒱.f j ≫ k) (𝒰.f i ≫ h)
  have hr : (e i j).opensRange = (r ≫ p).opensRange := by
    exact (hrange i j).trans (opensRange_iteratedPullbackFst f g (𝒰.f i) (𝒱.f j)).symm
  let E := IsOpenImmersion.isoOfRangeEq (e i j) (r ≫ p)
    (congrArg (fun U : W.Opens ↦ (U : Set W)) hr)
  have hE : E.hom ≫ r ≫ p = e i j := by
    exact IsOpenImmersion.isoOfRangeEq_hom_fac (e i j) (r ≫ p) _
  have hs : E.hom ≫ s = b i j := by
    apply (cancel_mono (𝒱.f j)).mp
    calc
      (E.hom ≫ s) ≫ 𝒱.f j = E.hom ≫ r ≫ (p ≫ g) := by
        dsimp [s, r]
        rw [Category.assoc, ← pullback.condition]
      _ = (E.hom ≫ r ≫ p) ≫ g := by simp only [Category.assoc]
      _ = e i j ≫ g := by rw [hE]
      _ = b i j ≫ 𝒱.f j := hb i j
  have hq : E.hom ≫ r ≫ q = a i j := by
    apply (cancel_mono (𝒰.f i)).mp
    calc
      (E.hom ≫ r ≫ q) ≫ 𝒰.f i = E.hom ≫ r ≫ (p ≫ f) := by
        dsimp [p, q]
        simp only [Category.assoc, ← pullback.condition]
      _ = (E.hom ≫ r ≫ p) ≫ f := by simp only [Category.assoc]
      _ = e i j ≫ f := by rw [hE]
      _ = a i j ≫ 𝒰.f i := ha i j
  exact (H i j).flip.of_iso E (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using hs.symm) (by simpa using hq.symm) (by simp) (by simp)

end SerrePositivity.AlgebraicGeometry
