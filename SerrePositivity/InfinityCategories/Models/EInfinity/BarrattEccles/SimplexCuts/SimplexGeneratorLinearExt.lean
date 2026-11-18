module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NormalizedGenerators
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GeneratorLinearExt

/-!
模型。文献の定義との比較は後で
# 元の二語の係数と一般の正規化単体生成元の外延性

Berger–Fresse §1.2.1・§2.2.6、M14 L14/L16、報告 §387。
同じ次数比較同型と既存の正規化生成元の外延性を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial _root_.TensorProduct
variable (A : Type u) [CommRing A]

/-- 同じ整数複体の負次数の線形写像は元の全単体生成元で決まる（BF §2.2.6）。 -/
lemma chains_generator_linear_ext (S : SSet.{0}) (q : ℕ)
    {M : Type u} [AddCommGroup M] [Module A M]
    {f g : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(q : ℤ)) →ₗ[A] M}
    (h : ∀ x : S _⦋q⦌, f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x) = g (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x)) : f = g := by
  have H : (ModuleCat.ofHom (f.comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).inv.hom) :
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).X q ⟶ ModuleCat.of A M) =
      ModuleCat.ofHom (g.comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).inv.hom) :=
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A S q h
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun l : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).X q ⟶ ModuleCat.of A M =>
    l ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).hom x)) H
  change f ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).inv ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).hom x)) =
    g ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).inv ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).hom x)) at hx
  simpa only [ModuleCat.inv_hom_apply] using hx

/-- 二つの元の語基底と全単体生成元による三重テンソルの外延性（BF §2.2.6）。 -/
lemma coefficient_simplex_linear_ext (S : SSet.{0}) (m n d e q : ℕ)
    {M : Type u} [AddCommGroup M] [Module A M]
    {f g : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A m).X (-(d : ℤ)) ⊗[A]
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(e : ℤ))) ⊗[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(q : ℤ)) →ₗ[A] M}
    (h : ∀ (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord m d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (x : S _⦋q⦌),
      f (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A m d).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A m d (ULift.up u)) ⊗ₜ[A]
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v))) ⊗ₜ[A]
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x) =
      g (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A m d).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A m d (ULift.up u)) ⊗ₜ[A]
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v))) ⊗ₜ[A]
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x)) :
    f = g := by
  apply TensorProduct.curry_injective
  apply TensorProduct.curry_injective
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.complex_basis_linear_ext A m d
  intro u
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.complex_basis_linear_ext A n e
  intro v
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains_generator_linear_ext A S q
  exact h u v

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
