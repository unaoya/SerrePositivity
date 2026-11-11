module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.RepresentableAddition

/-! # 対象の全射的な表示に沿う自然な演算の加法判定

概要：対象を全射的に表示する添字上で与えられた Hom の自然な零単位演算は既存の加法と一致する。
方針：二項双積の対象の表示を一つ選び、表示同型を介した二射影と余対角で計算する。
規約：対象の表示を大域的に選択して圏構造を作り直さない。使われ方：頂点表示のホモトピー圏の演算の照合。
-/
@[expose] public section
noncomputable section
universe w v u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：全射的な対象表示上の、後合成に自然で零単位を持つ射の演算は加法。
方針：双積の対象を表示して二つの射を別々の成分に入れ、射影で判定して余対角へ合成する。
規約：結合則や可換性は仮定しない。使われ方：全対象が頂点で表されるホモトピー圏への適用。 -/
lemma representableOperation_eq_add_of_surjective_objects
    {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
    {I : Type w} (obj : I → C) (hobj : Function.Surjective obj) (A : C)
    (μ : ∀ i : I, (A ⟶ obj i) → (A ⟶ obj i) → (A ⟶ obj i))
    (hleft : ∀ (i : I) (f : A ⟶ obj i), μ i 0 f = f)
    (hright : ∀ (i : I) (f : A ⟶ obj i), μ i f 0 = f)
    (hnat : ∀ (i j : I) (f g : A ⟶ obj i) (h : obj i ⟶ obj j),
      μ i f g ≫ h = μ j (f ≫ h) (g ≫ h))
    (i : I) (f g : A ⟶ obj i) : μ i f g = f + g := by
  obtain ⟨k, hk⟩ := hobj (obj i ⊞ obj i)
  let e : obj k ≅ obj i ⊞ obj i := eqToIso hk
  let u := biprod.lift f (0 : A ⟶ obj i) ≫ e.inv
  let v := biprod.lift (0 : A ⟶ obj i) g ≫ e.inv
  have hpair : μ k u v ≫ e.hom = biprod.lift f g := by
    apply biprod.hom_ext
    · rw [Category.assoc, hnat]
      simp only [u, v, Category.assoc, Iso.inv_hom_id_assoc, biprod.lift_fst, hright]
    · rw [Category.assoc, hnat]
      simp only [u, v, Category.assoc, Iso.inv_hom_id_assoc, biprod.lift_snd, hleft]
  have h := congrArg (fun t => t ≫ biprod.desc (𝟙 (obj i)) (𝟙 (obj i))) hpair
  rw [Category.assoc, hnat] at h
  simpa only [u, v, Category.assoc, Iso.inv_hom_id_assoc, biprod.lift_desc,
    Category.comp_id, zero_add, add_zero] using h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
