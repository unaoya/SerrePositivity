module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounitLaws
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCoassociativity
public import SerrePositivity.EInfinity.BarrattEccles.AugmentationValues

/-!
# Barratt–Eccles の整数複体の AW 対角

概要：Berger–Fresse §1.1.4 の AW 対角を既存の E(n) へ適用する。
方針：一般の整数コチェイン対角を EΣ_n に特殊化し自然性を右作用へ適用する。
規約：ここでは arity ごとの鎖写像を供給し、オペラッド合成との適合性は後続で証明する。
使われ方：E の Hopf オペラッド構造を組み立てる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：E(n) の AW 対角鎖写像（Berger–Fresse §1.1.4）。
方針：一般の正規化コチェイン対角を EΣ_n に適用する。
規約：既存の非有界整数コチェインテンソルを使う。
使われ方：Hopf オペラッドの対角の arity 成分。 -/
def complexDiagonal (n : ℕ) : complex A n ⟶ complex A n ⊗ complex A n :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A (simplicial n)

/-- 概要：E(n) の AW 対角は Σ_n 右作用と可換（Berger–Fresse §1.1.4）。
方針：一般の AW 対角の自然性を同時右乗法へ適用する。
規約：両出力因子に同じ置換を作用させる。
使われ方：Hopf 対角を対称列の射へ束ねる。 -/
lemma complexDiagonal_rightAction (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    complexRightAction A n σ ≫ complexDiagonal A n =
      complexDiagonal A n ≫
        HomologicalComplex.tensorHom (complexRightAction A n σ) (complexRightAction A n σ) :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_natural A (rightAction n σ)

/-- 概要：一般の AW 鎖余単位は既存の EΣ_n の収縮の順方向と一致（Berger–Fresse §1.1）。
方針：単一複体への射を零次の生成元で比較する。
規約：比較は鎖写像全体の等式である。
使われ方：AW 余単位と既存の E → Com の augmentation の同定。 -/
lemma chainCounit_eq_contraction (n : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A (simplicial n) = (normalizedChainContraction A n).hom := by
  apply HomologicalComplex.to_single_hom_ext
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit_f_zero]
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A (simplicial n) 0
  intro x
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A (simplicial n)
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (simplicial n) 0 x) =
    (normalizedChainContraction A n).hom.f 0 (normalizedGenerator A n 0 x)
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation_generator, normalizedAugmentation_generator_zero]

/-- 概要：整数 AW 余単位は既存の E(n) の augmentation に一致（Berger–Fresse §1.1）。
方針：鎖余単位と収縮の一致を同じ延長と single 比較で移す。
規約：新しい augmentation を既存のものと別に仮定しない。
使われ方：Hopf 余単位として既存の E → Com を利用する。 -/
lemma cochainCounit_eq_augmentation (n : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (simplicial n) = complexAugmentation A n := by
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit, chainCounit_eq_contraction]
  rfl

/-- 概要：E(n) の AW 対角は余結合的（Berger–Fresse §1.1.4）。
方針：一般の整数 AW 対角の余結合性を EΣ_n に適用する。
規約：実際の E(n) の整数コチェインテンソル上の等式である。
使われ方：Hopf オペラッド対角の余結合性。 -/
lemma complexDiagonal_coassoc (n : ℕ) :
    complexDiagonal A n ≫
        HomologicalComplex.tensorHom (complexDiagonal A n) (𝟙 (complex A n)) ≫
        (HomologicalComplex.associator (complex A n) (complex A n) (complex A n)).hom =
      complexDiagonal A n ≫
        HomologicalComplex.tensorHom (𝟙 (complex A n)) (complexDiagonal A n) :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_coassoc A (simplicial n)

/-- 概要：E(n) の既存の augmentation は AW 対角の左余単位（Berger–Fresse §1.1.4）。
方針：整数 AW の左余単位則で余単位と既存の augmentation の一致を使う。
規約：新しい augmentation や追加の仮定を導入しない。
使われ方：Hopf オペラッド射 E → E ⊗ E の左余単位。 -/
lemma complexDiagonal_left_counit (n : ℕ) :
    complexDiagonal A n ≫
        HomologicalComplex.tensorHom (complexAugmentation A n) (𝟙 (complex A n)) ≫
        (HomologicalComplex.leftUnitor (complex A n)).hom = 𝟙 _ := by
  have h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_left_counit A (simplicial n)
  rw [cochainCounit_eq_augmentation] at h
  exact h

/-- 概要：E(n) の既存の augmentation は AW 対角の右余単位（Berger–Fresse §1.1.4）。
方針：整数 AW の右余単位則で余単位と既存の augmentation の一致を使う。
規約：新しい augmentation や追加の仮定を導入しない。
使われ方：Hopf オペラッド射 E → E ⊗ E の右余単位。 -/
lemma complexDiagonal_right_counit (n : ℕ) :
    complexDiagonal A n ≫
        HomologicalComplex.tensorHom (𝟙 (complex A n)) (complexAugmentation A n) ≫
        (HomologicalComplex.rightUnitor (complex A n)).hom = 𝟙 _ := by
  have h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_right_counit A (simplicial n)
  rw [cochainCounit_eq_augmentation] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles
