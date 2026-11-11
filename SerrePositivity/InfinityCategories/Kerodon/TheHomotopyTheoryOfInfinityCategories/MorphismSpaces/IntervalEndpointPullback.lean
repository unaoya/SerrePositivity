module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor

/-!
概要：区間の端点の包含の自然性の正方形の pullback 性。
方針：直積の第一射影から持ち上げを取り、区間成分が指定端点であることを使う。
規約：底の単体集合の射に単射性を要求しない。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の fat join の単射保存。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間の端点 ₀ の包含の自然性の正方形は pullback。
方針：第一射影から一意な持ち上げを取り、第二射影を端点で計算する。
規約：射 f は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の円柱の部分の逆像。 -/
lemma isPullback_ι₀_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    IsPullback (SSet.ι₀ (X := A)) f (f ▷ (Δ[1] : SSet.{u})) SSet.ι₀ := by
  apply IsPullback.mk' (SSet.ι₀_comp f)
  · intro T φ ψ h₁ h₂
    simpa using h₁ =≫ fst A (Δ[1] : SSet.{u})
  · intro T a b h
    refine ⟨a ≫ fst A (Δ[1] : SSet.{u}), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · have he := h =≫ snd B (Δ[1] : SSet.{u})
        simpa only [Category.assoc, whiskerRight_snd, SSet.ι₀_snd,
          SSet.comp_const] using he.symm
    · have he := h =≫ fst B (Δ[1] : SSet.{u})
      simpa only [Category.assoc, whiskerRight_fst, SSet.ι₀_fst, Category.comp_id] using he

/-- 概要：区間の端点 ₁ の包含の自然性の正方形は pullback。
方針：第一射影から一意な持ち上げを取り、第二射影を端点で計算する。
規約：射 f は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の円柱の部分の逆像。 -/
lemma isPullback_ι₁_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    IsPullback (SSet.ι₁ (X := A)) f (f ▷ (Δ[1] : SSet.{u})) SSet.ι₁ := by
  apply IsPullback.mk' (SSet.ι₁_comp f)
  · intro T φ ψ h₁ h₂
    simpa using h₁ =≫ fst A (Δ[1] : SSet.{u})
  · intro T a b h
    refine ⟨a ≫ fst A (Δ[1] : SSet.{u}), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · have he := h =≫ snd B (Δ[1] : SSet.{u})
        simpa only [Category.assoc, whiskerRight_snd, SSet.ι₁_snd,
          SSet.comp_const] using he.symm
    · have he := h =≫ fst B (Δ[1] : SSet.{u})
      simpa only [Category.assoc, whiskerRight_fst, SSet.ι₁_fst, Category.comp_id] using he

/-- 概要：第一射影の自然性の正方形は pullback。
方針：直積の二つの成分から持ち上げを取る。
規約：射 f と固定因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の fat join の零端の計算。 -/
lemma isPullback_fst_whiskerRight {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    IsPullback (fst A K) (f ▷ K) f (fst B K) := by
  apply IsPullback.mk' (whiskerRight_fst f K).symm
  · intro T φ ψ h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · exact h₁
    · simpa using h₂ =≫ snd B K
  · intro T a b h
    refine ⟨lift a (b ≫ snd B K), by simp, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h
    · simp

/-- 概要：区間の端点 ₀ の包含は単射。
方針：第一射影との合成が恒等であることを使う。
規約：任意の単体集合 A を扱う。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の貼り合わせ。 -/
instance intervalEndpoint₀_mono (A : SSet.{u}) : Mono (SSet.ι₀ (X := A)) := by
  constructor
  intro T f g h
  simpa using h =≫ fst A (Δ[1] : SSet.{u})

/-- 概要：区間の端点 ₁ の包含は単射。
方針：第一射影との合成が恒等であることを使う。
規約：任意の単体集合 A を扱う。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の貼り合わせ。 -/
instance intervalEndpoint₁_mono (A : SSet.{u}) : Mono (SSet.ι₁ (X := A)) := by
  constructor
  intro T f g h
  simpa using h =≫ fst A (Δ[1] : SSet.{u})

/-- 概要：固定した因子との直積は pullback を保つ。
方針：元の pullback の持ち上げと固定因子への射を組にする。
規約：単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の円柱の正方形。 -/
lemma isPullback_whiskerRight {P A B C : SSet.{u}}
    {i : P ⟶ A} {j : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback i j f g) (K : SSet.{u}) :
    IsPullback (i ▷ K) (j ▷ K) (f ▷ K) (g ▷ K) := by
  apply IsPullback.mk' (by rw [← MonoidalCategory.comp_whiskerRight,
    ← MonoidalCategory.comp_whiskerRight, h.w])
  · intro T φ ψ h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · apply h.hom_ext
      · simpa using h₁ =≫ fst A K
      · simpa using h₂ =≫ fst B K
    · simpa using h₁ =≫ snd A K
  · intro T a b hab
    have hf : (a ≫ fst A K) ≫ f = (b ≫ fst B K) ≫ g := by
      simpa using hab =≫ fst C K
    refine ⟨lift (h.lift (a ≫ fst A K) (b ≫ fst B K) hf) (a ≫ snd A K), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext <;> simp
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa using hab =≫ snd C K

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
