module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.ChainDiagonal
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.TensorAssociator

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

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：AW 対角鎖写像は余結合的（Berger–Fresse §1.1.4）。
方針：二段階の有限射影で component_coassoc に帰着する。
規約：テンソルの結合子以外の比較同型を追加しない。
使われ方：Hopf 対角の余結合性を鎖写像として供給する。 -/
lemma diagonal_coassoc (X : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X ≫ HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X) (𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)) ≫
        (HomologicalComplex.associator (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)).hom =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X ≫ HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection_hom_ext
  intro p s hps
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.whiskerLeft_tensorProjection_hom_ext
  intro q r hqr
  have hn : n = p + q + r := by omega
  cases hn
  subst s
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorAssociator_projection]
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorHom_projection_assoc, HomologicalComplex.id_f,
    MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom,
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_projection_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.whiskerLeft_comp, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_projection]
  exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_coassoc A X p q r

end SerrePositivity.SimplicialChains.AlexanderWhitney
