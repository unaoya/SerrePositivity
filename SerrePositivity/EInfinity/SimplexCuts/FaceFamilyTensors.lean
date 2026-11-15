module

public import SerrePositivity.EInfinity.SimplexCuts.CutTensor

/-!
# 同じ指定面の全族を元の斉次テンソルへ運ぶ

Berger–Fresse §2.2.6、M14 L12a の証明分割、報告 §292。
元の正規化生成元・右括弧テンソルを保ち、次数の移送だけを異種等式で記す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 等しい指定面の族と等しい整数係数は同じ斉次実テンソルを与える（BF §2.2.6）。 -/
lemma faceFamily_tensor_heq (A : Type u) [CommRing A] (S : SSet.{0}) {r q : ℕ}
    (F G : Fin r → Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) (h : F = G)
    (x : S _⦋q⦌) (a b : ℤ) (hab : a = b) :
    HEq
      (a • tensorValue (chains A S) r (fun i => (F i).1)
        (fun i => gen A S (F i).1 (S.map (SimplexCategory.mkHom (F i).2).op x)))
      (b • tensorValue (chains A S) r (fun i => (G i).1)
        (fun i => gen A S (G i).1 (S.map (SimplexCategory.mkHom (G i).2).op x))) := by
  subst G
  subst b
  rfl

/-- 同じ合成面の生成元は、元の二つの面を続けて作用させた生成元（BF §2.2.6）。 -/
lemma gen_map_comp_faces (A : Type u) [CommRing A] (S : SSet.{0})
    {a b q : ℕ} (f : Fin (b + 1) →o Fin (q + 1))
    (g : Fin (a + 1) →o Fin (b + 1)) (x : S _⦋q⦌) :
    gen A S a (S.map (SimplexCategory.mkHom (f.comp g)).op x) =
      gen A S a (S.map (SimplexCategory.mkHom g).op
        (S.map (SimplexCategory.mkHom f).op x)) := by
  have h : SimplexCategory.mkHom (f.comp g) =
      SimplexCategory.mkHom g ≫ SimplexCategory.mkHom f := rfl
  rw [h, op_comp, S.map_comp]
  rfl

end SerrePositivity.EInfinity.SimplexCuts
