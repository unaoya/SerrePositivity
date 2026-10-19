module

public import SerrePositivity.EInfinity.AlexanderWhitney.ChainDiagonal
public import SerrePositivity.EInfinity.AlexanderWhitney.TensorAssociator

/-!
# AW 鎖写像の余結合性

概要：Berger–Fresse §1.1.4 の余結合性を鎖写像の等式として証明する。
方針：三重テンソルの全ての次数への射影を取り、成分の余結合性を使う。
規約：既存の複体の結合子により右結合へ揃える。
使われ方：Barratt–Eccles の Hopf オペラッドの余結合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.AlexanderWhitney

open CategoryTheory MonoidalCategory HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：AW 対角鎖写像は余結合的（Berger–Fresse §1.1.4）。
方針：二段階の有限射影で component_coassoc に帰着する。
規約：テンソルの結合子以外の比較同型を追加しない。
使われ方：Hopf 対角の余結合性を鎖写像として供給する。 -/
lemma diagonal_coassoc (X : SSet.{0}) :
    diagonal A X ≫ HomologicalComplex.tensorHom (diagonal A X) (𝟙 (chains A X)) ≫
        (HomologicalComplex.associator (chains A X) (chains A X) (chains A X)).hom =
      diagonal A X ≫ HomologicalComplex.tensorHom (𝟙 (chains A X)) (diagonal A X) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensorProjection_hom_ext
  intro p s hps
  apply whiskerLeft_tensorProjection_hom_ext
  intro q r hqr
  have hn : n = p + q + r := by omega
  cases hn
  subst s
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [tensorAssociator_projection]
  simp only [tensorHom_projection_assoc, HomologicalComplex.id_f,
    MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom,
    diagonal_projection_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.whiskerLeft_comp, diagonal_projection]
  exact component_coassoc A X p q r

end SerrePositivity.EInfinity.AlexanderWhitney
