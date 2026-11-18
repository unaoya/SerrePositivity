module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssembly

/-!
模型。文献の定義との比較は後で
# Convolution の入力ブロックの移送

概要：Berger–Fresse §3.1 の組み立ての係数を固定して入力と中間評価を移す。
方針：一般の組み立ての自然性に恒等射を代入する。
規約：移送する射は同型である必要はない。
使われ方：連結した反復入力と二つの独立な入力ブロックの表示を比較する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {K : Type u} [Category.{v} K] [MonoidalCategory K] [SymmetricCategory K]

/-- 概要：係数を固定した組み立ては中間の入力の移送を保つ（BF §3.1）。
方針：一般の自然性で係数・評価点・最終出力の射を恒等射にする。
規約：余演算・評価・作用の三つの比較図式を仮定する。
使われ方：先頭への代入の評価を余代入の組み立てへ変換する。 -/
lemma convolutionAssembly_transport {O C D V H W T B V' W' T' : K}
    (d : O ⟶ C ⊗ D) (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B)
    (θ' : D ⊗ H ⟶ W') (e' : V' ⊗ W' ⟶ T') (a' : C ⊗ T' ⟶ B)
    (v : V ⟶ V') (w : W ⟶ W') (t : T ⟶ T')
    (hθ : θ' = θ ≫ w) (he : (v ⊗ₘ w) ≫ e' = e ≫ t)
    (ha : (C ◁ t) ≫ a' = a) :
    ((O ◁ v) ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ' e' a' =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e a := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_naturality d θ e a d θ' e' a'
    (𝟙 O) (𝟙 C) (𝟙 D) v (𝟙 H) w t (𝟙 B)
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
    (by simpa only [tensorHom_id, id_whiskerRight, Category.id_comp] using hθ)
    he (by simpa only [id_tensorHom, Category.comp_id] using ha)
  simpa only [tensorHom_id, id_tensorHom, Category.comp_id] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
