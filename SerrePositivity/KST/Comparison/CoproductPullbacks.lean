module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# 二項余積と厳密な引き戻し

概要：単体集合の二項余積の包含と、二つの引き戻しの余積を扱う。
方針：前層圏の extensive 性から得られる二項余積の van Kampen 性を使う。
規約：Segal 1974 Lemma 1.7 の厳密な引き戻しの部分の補助。
使われ方：二重写像円筒の左右の脚を一つの pushout の脚へまとめる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：二項余積の包含の自然性の二つの四角形は引き戻しである。
方針：余積の van Kampen 条件の逆向きを、上側の余積の普遍性に適用する。
規約：任意の二射に対する厳密な引き戻し。
使われ方：余積を取った引き戻しの証明と、左右の脚の取り出し。
-/
theorem coproductInclusions_isPullback {A B A' B' : SSet.{u}}
    (a : A ⟶ A') (b : B ⟶ B') :
    IsPullback coprod.inl a (coprod.map a b) coprod.inl ∧
      IsPullback coprod.inr b (coprod.map a b) coprod.inr := by
  exact ((BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod A' B'))
      (BinaryCofan.mk coprod.inl coprod.inr) a b (coprod.map a b)
      (by simp) (by simp)).mp ⟨coprodIsCoprod A B⟩

/--
概要：同じ底の射に対する二つの引き戻しを、底の二項余積に沿って貼り合わせる。
方針：実際の引き戻しへの二射が余積をなすことを van Kampen 性で示す。
規約：Segal Lemma 1.7 の厳密な版のための有限余積の普遍性。
使われ方：二つの引き戻しの余積の引き戻し性。
-/
theorem binaryCoproductPullback {A₀ A₁ C₀ C₁ B D : SSet.{u}}
    (q₀ : A₀ ⟶ B) (q₁ : A₁ ⟶ B) (t₀ : A₀ ⟶ C₀) (t₁ : A₁ ⟶ C₁)
    (v : B ⟶ D) (w : C₀ ⨿ C₁ ⟶ D)
    (h₀ : IsPullback q₀ t₀ v (coprod.inl ≫ w))
    (h₁ : IsPullback q₁ t₁ v (coprod.inr ≫ w)) :
    IsPullback (coprod.desc q₀ q₁) (coprod.map t₀ t₁) v w := by
  let l₀ : A₀ ⟶ pullback v w := pullback.lift q₀ (t₀ ≫ coprod.inl) (by simpa using h₀.w)
  let l₁ : A₁ ⟶ pullback v w := pullback.lift q₁ (t₁ ≫ coprod.inr) (by simpa using h₁.w)
  have k₀ : IsPullback l₀ t₀ (pullback.snd v w) coprod.inl := by
    apply IsPullback.of_right (by simpa [l₀] using h₀) (by simp [l₀])
      (IsPullback.of_hasPullback v w)
  have k₁ : IsPullback l₁ t₁ (pullback.snd v w) coprod.inr := by
    apply IsPullback.of_right (by simpa [l₁] using h₁) (by simp [l₁])
      (IsPullback.of_hasPullback v w)
  obtain ⟨hc⟩ := ((BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod C₀ C₁))
      (BinaryCofan.mk l₀ l₁) t₀ t₁ (pullback.snd v w)
      (by simp [l₀]) (by simp [l₁])).mpr ⟨k₀, k₁⟩
  let e := (coprodIsCoprod A₀ A₁).coconePointUniqueUpToIso hc
  have he₀ : coprod.inl ≫ e.hom = l₀ :=
    (coprodIsCoprod A₀ A₁).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.left⟩
  have he₁ : coprod.inr ≫ e.hom = l₁ :=
    (coprodIsCoprod A₀ A₁).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.right⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ e ?_ ?_
  · apply coprod.hom_ext
    · simpa using h₀.w
    · simpa using h₁.w
  · apply coprod.hom_ext
    · rw [← Category.assoc, he₀]; simp [l₀]
    · rw [← Category.assoc, he₁]; simp [l₁]
  · apply coprod.hom_ext
    · rw [← Category.assoc, he₀]; simp [l₀]
    · rw [← Category.assoc, he₁]; simp [l₁]

/--
概要：二つの厳密な引き戻しの四角形の二項余積は厳密な引き戻しである。
方針：余積の包含との引き戻しの貼り合わせと、底の余積に沿う普遍性を使う。
規約：ホモトピー引き戻しへの移行は含めない。
使われ方：二重写像円筒の van Kampen の立方体の左右の面。
-/
theorem coproductSquare_isPullback {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : SSet.{u}}
    {f₀ : A₀ ⟶ B₀} {f₁ : A₁ ⟶ B₁} {g₀ : A₀ ⟶ C₀} {g₁ : A₁ ⟶ C₁}
    {v₀ : B₀ ⟶ D₀} {v₁ : B₁ ⟶ D₁} {w₀ : C₀ ⟶ D₀} {w₁ : C₁ ⟶ D₁}
    (h₀ : IsPullback f₀ g₀ v₀ w₀) (h₁ : IsPullback f₁ g₁ v₁ w₁) :
    IsPullback (coprod.map f₀ f₁) (coprod.map g₀ g₁)
      (coprod.map v₀ v₁) (coprod.map w₀ w₁) := by
  have k₀ := h₀.paste_horiz (coproductInclusions_isPullback v₀ v₁).1
  have k₁ := h₁.paste_horiz (coproductInclusions_isPullback v₀ v₁).2
  have h := binaryCoproductPullback (f₀ ≫ coprod.inl) (f₁ ≫ coprod.inr) g₀ g₁
    (coprod.map v₀ v₁) (coprod.map w₀ w₁)
    (by simpa using k₀) (by simpa using k₁)
  convert h using 1
  apply coprod.hom_ext <;> simp

end SerrePositivity.KST.Comparison
