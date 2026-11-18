module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssemblyComposition

/-!
模型。文献の定義との比較は後で
# Convolution の始域についての自然性

概要：Berger–Fresse §3.1 の組み立てで、関数の前合成と評価点の写像を比較する。
方針：入力と評価点についての自然性を同じ中間図式へ結ぶ。
規約：係数・作用・最終出力は固定する。
使われ方：余代数射による convolution の前合成が演算を保つことを示す。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {K : Type u} [Category.{v} K] [MonoidalCategory K] [SymmetricCategory K]

/-- 概要：始域の写像による前合成と評価は組み立ての中でも一致する（BF §3.1）。
方針：係数を固定した一般の自然性を使い、入力への射を評価へ移す。
規約：余演算と反復評価の二つの比較図式を仮定する。
使われ方：余代数射の前合成の自然性を複体へ特殊化する。 -/
lemma convolutionAssembly_pre {O C D V V' H H' W W' T B : K}
    (d : O ⟶ C ⊗ D) (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B)
    (θ' : D ⊗ H' ⟶ W') (e' : V' ⊗ W' ⟶ T)
    (v : V ⟶ V') (k : H' ⟶ H) (w : W' ⟶ W)
    (hθ : (D ◁ k) ≫ θ = θ' ≫ w)
    (he : (v ▷ W') ≫ e' = (V ◁ w) ≫ e) :
    ((O ◁ v) ▷ H') ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ' e' a =
      ((O ⊗ V) ◁ k) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e a := by
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_naturality d θ' ((V ◁ w) ≫ e) a d θ e a
    (𝟙 O) (𝟙 C) (𝟙 D) (𝟙 V) k w (𝟙 T) (𝟙 B)
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
    (by simpa only [id_tensorHom] using hθ)
    (by simp only [id_tensorHom, Category.comp_id])
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
  simp only [tensorHom_id, id_whiskerRight, id_tensorHom, Category.comp_id] at hn
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_input, he]
  exact hn.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
