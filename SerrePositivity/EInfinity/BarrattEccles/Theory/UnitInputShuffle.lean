module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.StandardTensorSeparation

/-!
# 二つの単位入力の並べ替え

HA 3.2.4.7 の指定 Hopf 入力の計算で使う照合 I3。
既存の tensorμ と単位子から作った同じ射を、二通りの順序で書いた式を比較する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {R : Type u} [CommRing R]

/-- 四因子の中央の二つが単位から来るときの、指定 shuffle の自然性。 -/
lemma tensorμ_unit_insert {X Y K L M N : Complex R}
    (f : X ⟶ K) (u : 𝟙_ (Complex R) ⟶ L)
    (v : 𝟙_ (Complex R) ⟶ M) (g : Y ⟶ N) :
    (((ρ_ X).inv ≫ (f ⊗ₘ u)) ⊗ₘ ((λ_ Y).inv ≫ (v ⊗ₘ g))) ≫
      tensorμ K L M N =
    ((ρ_ X).inv ≫ (f ⊗ₘ v)) ⊗ₘ ((λ_ Y).inv ≫ (u ⊗ₘ g)) := by
  rw [← tensorHom_comp_tensorHom_assoc, tensorμ_natural,
    ← tensorHom_comp_tensorHom]
  congr 1
  dsimp only [tensorμ]
  rw [braiding_tensorUnit_left]
  monoidal

end SerrePositivity.EInfinity
