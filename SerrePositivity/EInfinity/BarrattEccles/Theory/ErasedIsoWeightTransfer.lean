module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.WeightBasisEquiv
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseAlgebraWordAction

/-!
# 微分を消した同型による代数作用の重みの移送

## 概要
Berger–Moerdijk §1 の自由表示と同じ語の基底を持つ代数で、作用の重み保存を移す。

## 方針
同型で斉次作用を比較し、次数ごとの線形同型で重み付き部分加群を移す。

## 規約
同型を仮定するのは微分を消した代数の間だけ。

## 使われ方
自由代数の作用の重み評価から、実際のセル段の作用の重み評価を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open scoped TensorProduct
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {X Y : P.Algebra} {I : ℤ → Type u}

/-- Action weight bounds descend through a basis-compatible isomorphism after erasure. -/
lemma action_weightBound_of_erasedIso
    (e : P.eraseAlgebra.obj X ≅ P.eraseAlgebra.obj Y)
    (b : ∀ i, Module.Basis (I i) A (X.carrier.X i))
    (c : ∀ i, Module.Basis (I i) A (Y.carrier.X i))
    (he : ∀ i z, e.hom.hom.f i (b i z) = c i z) (w : (Σ i, I i) → ℕ)
    (hY : ∀ (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p) (N : ℕ)
        {v : (power Y.carrier n).X r},
      v ∈ basisWeightSpan (powerGradedBasis c n r) (powerGradedWeight w n r) N →
      (Y.action n).f i (ιTensorObj (P.arity n) (power Y.carrier n) p r i h (u ⊗ₜ[A] v)) ∈
        basisWeightSpan (c i) (fun z => w ⟨i, z⟩) N)
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p) (N : ℕ)
    {v : (power X.carrier n).X r}
    (hv : v ∈ basisWeightSpan (powerGradedBasis b n r) (powerGradedWeight w n r) N) :
    (X.action n).f i (ιTensorObj (P.arity n) (power X.carrier n) p r i h (u ⊗ₜ[A] v)) ∈
      basisWeightSpan (b i) (fun z => w ⟨i, z⟩) N := by
  let f : (power X.carrier n).X r →ₗ[A] X.carrier.X i :=
    ((X.action n).f i).hom ∘ₗ (ιTensorObj (P.arity n) (power X.carrier n) p r i h).hom ∘ₗ
      (TensorProduct.mk A _ _ u)
  change f v ∈ _
  apply map_mem_basisWeightSpan (powerGradedBasis b n r) (b i)
    (powerGradedWeight w n r) (fun z => w ⟨i, z⟩) f ?_ N hv
  intro x
  let q := (HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).mapIso
    (X := (eraseDifferential A).obj X.carrier)
    (Y := (eraseDifferential A).obj Y.carrier) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).mapIso e)
  apply (mem_basisWeightSpan_iff_map (b i) (c i) q.toLinearEquiv
    (fun z => he i z) (fun z => w ⟨i, z⟩) _ _).mpr
  change e.hom.hom.f i ((X.action n).f i
    (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerGradedBasis b n r x))) ∈ _
  rw [erasedIso_action_basis e b c he]
  exact hY n p r i h u _
    (basis_mem_basisWeightSpan (powerGradedBasis c n r) (powerGradedWeight w n r) x)

end SerrePositivity.EInfinity.Operad
