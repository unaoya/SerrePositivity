module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionOperations
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionEquivariantEvaluation

/-!
模型。文献の定義との比較は後で
# Convolution の等変性

概要：Berger–Fresse §3.1 の convolution は係数と入力の同時置換で不変である。
方針：Hopf 対角の自然性、余演算の等変性、反復評価、代数の等変性を組み合わせる。
規約：全 arity と全置換を扱い、次数による切り捨てはしない。
使われ方：内部 Hom の P 代数構造の対称群の公理となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：評価後の convolution は係数と入力の同時置換で不変（BF §3.1）。
方針：各段の等変性を組み立ての自然性へ代入する。
規約：評価点 H の入力は置換しない。
使われ方：右転置後の convolution の等変性を導く。 -/
lemma convolutionUncurriedAction_equivariance (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra)
    (B : P.Algebra) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction (homComplex A H.carrier B.carrier) n σ).asIso.hom) ▷ H.carrier) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction hP H B n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction hP H B n := by
  have hd : P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ≫
      hP.diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n) =
      hP.diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n) ≫
        (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
          P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ)) :=
    hP.diagonal.map.naturality (_root_.SerrePositivity.FiniteBijection.permutation n σ)
  have hθ : (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ 𝟙 H.carrier) ≫
      H.coaction n = H.coaction n ≫ (permutationAction H.carrier n σ).asIso.hom := by
    rw [tensorHom_id]
    exact H.equivariance n σ
  have ha : (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction B.carrier n σ).asIso.hom) ≫ B.action n = B.action n ≫ 𝟙 _ := by
    rw [Category.comp_id]
    exact B.equivariance n σ
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_permutation H.carrier B.carrier n σ
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_naturality
    (hP.diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n)) (H.coaction n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n) (B.action n)
    (hP.diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n)) (H.coaction n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n) (B.action n)
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ))
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ))
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ))
    (permutationAction (homComplex A H.carrier B.carrier) n σ).asIso.hom (𝟙 H.carrier)
    (permutationAction H.carrier n σ).asIso.hom
    (permutationAction B.carrier n σ).asIso.hom (𝟙 B.carrier) hd hθ he ha
  simp only [tensorHom_id, Category.comp_id] at hn
  convert hn using 1 <;> rfl

/-- 概要：convolution 演算は P 代数の対称群等変性を満たす（BF §3.1）。
方針：同時置換を右 tensor 転置の自然性で評価後へ移す。
規約：任意の対称群の元に対して成り立つ。
使われ方：convolution を P 代数へ束ねる等変性条件となる。 -/
lemma convolutionAction_equivariance (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) (B : P.Algebra)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction (homComplex A H.carrier B.carrier) n σ).asIso.hom) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction, ← curryRight_naturality_source, tensorHom_id,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction_equivariance]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
