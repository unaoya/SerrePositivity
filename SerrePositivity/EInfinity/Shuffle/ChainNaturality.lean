module

public import SerrePositivity.EInfinity.Shuffle.ChainMap

/-!
# 一般 shuffle 鎖写像の自然性と生成元公式

概要：Berger–Fresse §1.1.3 の shuffle の成分公式を実際の鎖写像へ接続する。
方針：テンソルの斉次包含で検査し、成分の自然性を適用する。
規約：二入力の単体集合の射を独立に扱う。
使われ方：単体的合成による shuffle から Barratt–Eccles の部分合成を復元する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Shuffle

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped Simplicial TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：テンソル鎖写像の斉次包含上の公式（BF §1.1.3）。
方針：二変数全複体の射の包含公式をテンソル積の射へ読み替える。
規約：自然数鎖次数を使う。
使われ方：shuffle 鎖写像の自然性。 -/
@[reassoc]
lemma tensorHom_inclusion {K L K' L' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (p q : ℕ) :
    ιTensorObj K L p q (p + q) rfl ≫ (HomologicalComplex.tensorHom f g).f (p + q) =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj K' L' p q (p + q) rfl := by
  rw [ι_mapBifunctorMap]
  simp only [tensorHom_def, Category.assoc]
  rfl

/-- 概要：一般 shuffle 鎖写像は二入力に自然（BF §1.1.3）。
方針：斉次包含で検査し、shuffle 成分の自然性へ帰着する。
規約：退化する像にも成立する。
使われ方：単体的写像との合成と Hopf 合成の比較。 -/
lemma chainMap_natural {X X' Y Y' : SSet.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    HomologicalComplex.tensorHom (AlexanderWhitney.chainMap A f) (AlexanderWhitney.chainMap A g) ≫
        chainMap A X' Y' =
      chainMap A X Y ≫ AlexanderWhitney.chainMap A (f ⊗ₘ g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  subst n
  simp only [HomologicalComplex.comp_f]
  rw [tensorHom_inclusion_assoc, ι_chainMap, ι_chainMap_assoc]
  exact component_natural A f g p q

/-- 概要：一般 shuffle 鎖写像の生成元公式（BF §1.1.3）。
方針：斉次包含上の成分公式を生成元の純テンソルで評価する。
規約：入力単体が退化していてもよい。
使われ方：shuffle 和の余代数適合性を鎖写像の等式へ移す。 -/
lemma chainMap_generators (X Y : SSet.{0}) (p q : ℕ)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (chainMap A X Y).f (p + q)
        (ιTensorObj (AlexanderWhitney.chains A X) (AlexanderWhitney.chains A Y)
          p q (p + q) rfl (AlexanderWhitney.generator A X p x ⊗ₜ[A]
            AlexanderWhitney.generator A Y q y)) = value A X Y p q x y := by
  have he := congrArg (fun φ => φ (AlexanderWhitney.generator A X p x ⊗ₜ[A]
    AlexanderWhitney.generator A Y q y)) (ι_chainMap A X Y p q)
  exact he.trans (component_generators A X Y p q x y)

end SerrePositivity.EInfinity.Shuffle
