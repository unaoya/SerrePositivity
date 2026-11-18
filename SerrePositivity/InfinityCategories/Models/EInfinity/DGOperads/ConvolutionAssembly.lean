module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality

/-!
模型。文献の定義との比較は後で
# Convolution 図式の自然性

概要：Berger–Fresse §3.1 の係数分配・余演算・評価・作用の合成を比較する。
方針：各段の可換図式を tensorμ と結合子の自然性で連結する。
規約：一般の対称モノイダル圏で各対象の射を独立に動かす。
使われ方：convolution の等変性と両変数の関手性を一つの図式補題から証明する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {K : Type u} [Category.{v} K] [MonoidalCategory K] [SymmetricCategory K]

/-- 概要：convolution の評価後の組み立て（BF §3.1）。
方針：係数を分配し、第二係数の余演算、評価、第一係数の作用を適用する。
規約：複体の次数やオペラッドの公理に依存しない射の合成とする。
使われ方：自然性の図式を実際の convolution 演算へ特殊化する。 -/
def convolutionAssembly {O C D V H W T B : K} (d : O ⟶ C ⊗ D)
    (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B) :
    (O ⊗ V) ⊗ H ⟶ B :=
  ((d ▷ V) ▷ H) ≫ (α_ (C ⊗ D) V H).hom ≫ tensorμ C D V H ≫
    ((C ⊗ V) ◁ θ) ≫ (α_ C V W).hom ≫ (C ◁ e) ≫ a

/-- 概要：組み立ては各段の可換図式を保存する（BF §3.1）。
方針：テンソルの合成保存と結合子・分離の自然性で射を順に通す。
規約：全ての対象の射は独立でよく、同型である必要はない。
使われ方：等変性、余代数射の前合成、代数射の後合成を証明する。 -/
lemma convolutionAssembly_naturality {O C D V H W T B O' C' D' V' H' W' T' B' : K}
    (d : O ⟶ C ⊗ D) (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B)
    (d' : O' ⟶ C' ⊗ D') (θ' : D' ⊗ H' ⟶ W')
    (e' : V' ⊗ W' ⟶ T') (a' : C' ⊗ T' ⟶ B')
    (f : O ⟶ O') (c : C ⟶ C') (g : D ⟶ D') (v : V ⟶ V') (k : H ⟶ H')
    (w : W ⟶ W') (t : T ⟶ T') (b : B ⟶ B')
    (hd : f ≫ d' = d ≫ (c ⊗ₘ g)) (hθ : (g ⊗ₘ k) ≫ θ' = θ ≫ w)
    (he : (v ⊗ₘ w) ≫ e' = e ≫ t) (ha : (c ⊗ₘ t) ≫ a' = a ≫ b) :
    ((f ⊗ₘ v) ⊗ₘ k) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d' θ' e' a' =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e a ≫ b := by
  have hd' : ((f ⊗ₘ v) ⊗ₘ k) ≫ ((d' ▷ V') ▷ H') =
      ((d ▷ V) ▷ H) ≫ (((c ⊗ₘ g) ⊗ₘ v) ⊗ₘ k) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, hd]
  have hθ' : ((c ⊗ₘ v) ⊗ₘ (g ⊗ₘ k)) ≫ ((C' ⊗ V') ◁ θ') =
      ((C ⊗ V) ◁ θ) ≫ ((c ⊗ₘ v) ⊗ₘ w) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, hθ]
  have he' : (c ⊗ₘ (v ⊗ₘ w)) ≫ (C' ◁ e') = (C ◁ e) ≫ (c ⊗ₘ t) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, he]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, Category.assoc]
  rw [reassoc_of% hd', associator_naturality_assoc, tensorμ_natural_assoc,
    reassoc_of% hθ', associator_naturality_assoc, reassoc_of% he', ha]


/-- 概要：組み立ての入力関数と出力への後合成は両立する（BF §3.1）。
方針：係数・評価点を固定した組み立ての自然性へ帰着する。
規約：入力の射 v と出力の射 b の間を評価の射 t で比較する。
使われ方：代数射に沿う convolution の後合成を証明する。 -/
lemma convolutionAssembly_post {O C D V H W T B V' T' B' : K}
    (d : O ⟶ C ⊗ D) (θ : D ⊗ H ⟶ W)
    (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B)
    (e' : V' ⊗ W ⟶ T') (a' : C ⊗ T' ⟶ B')
    (v : V ⟶ V') (t : T ⟶ T') (b : B ⟶ B')
    (he : (v ▷ W) ≫ e' = e ≫ t) (ha : (C ◁ t) ≫ a' = a ≫ b) :
    ((O ◁ v) ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e' a' =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e a ≫ b := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_naturality d θ e a d θ e' a'
    (𝟙 O) (𝟙 C) (𝟙 D) v (𝟙 H) (𝟙 W) t b
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
    (by simpa only [tensorHom_id] using he)
    (by simpa only [id_tensorHom] using ha)
  simpa only [tensorHom_id, id_tensorHom] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
