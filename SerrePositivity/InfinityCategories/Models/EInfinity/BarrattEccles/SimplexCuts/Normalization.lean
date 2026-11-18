module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DegenerateInput
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Complex
public import Mathlib.LinearAlgebra.BilinearMap

/-!
模型。文献の定義との比較は後で
# BF 切断和の正規化への降下

Berger–Fresse §2.2.6。入力退化の消滅により、自由な単体の上の切断和を
同じ Moore 正規化へ降ろす（5a-5a L08）。係数と入力の双方の指定比較を保持する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.AlgebraicTopology _root_.AlgebraicTopology.DoldKan
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- L07 の線形な帰結：任意の同じ係数でも退化入力を消す。 -/
lemma rawComponent_degenerate (S : SSet.{0}) {r d q : ℕ}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (r + 1) d) (i : Fin (q + 1)) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d (q + 1) c (ModuleCat.freeMk (ULift.up (S.σ i x))) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add c e hc he => simp only [map_add, LinearMap.add_apply, hc, he, zero_add]
  | single c b =>
    have hs : Finsupp.single c b = b • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) d c := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis_apply, Finsupp.smul_single', mul_one]
    rw [hs, map_smul, LinearMap.smul_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_value, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum_degenerate, smul_zero]

/-- L08 の証明の分割：退化との合成が零という射の式。 -/
lemma rawComponent_sigma (S : SSet.{0}) {r d q : ℕ}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (r + 1) d) (i : Fin (q + 1)) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S).σ i ≫
      ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d (q + 1) c) = 0 := by
  apply ModuleCat.free_hom_ext
  intro ⟨x⟩
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d (q + 1) c
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S).σ i (ModuleCat.freeMk (ULift.up x))) = 0
  have h : ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S).σ i (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (S.σ i x)) := ModuleCat.free_map_apply _ _
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_degenerate A S c i x

/-- Moore 包含を前置した、正規化した双線形成分（BF §2.2.6）。 -/
def normalizedComponent (S : SSet.{0}) (r d q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (r + 1) d →ₗ[A] (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).X q →ₗ[A]
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q).compl₂
    ((inclusionOfMooreComplexMap ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S)).f q).hom

/-- L08 の証明の分割：正規化した生成元でも同じ自由加群上の値を復元する。 -/
lemma normalizedComponent_gen (S : SSet.{0}) {r d q : ℕ}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (r + 1) d) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent A S r d q c (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A S q x) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q c (ModuleCat.freeMk (ULift.up x)) := by
  have h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization_restrictToNormalized
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S) q (ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q c))
    (fun k e i => by subst q; simpa using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_sigma A S c i)
  exact ConcreteCategory.congr_hom h (ModuleCat.freeMk (ULift.up x))

/-- 正の arity の負自然数次数における同じ整数複体の成分。 -/
def positiveComponent (S : SSet.{0}) (r d q : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).X (-(d : ℤ)) →ₗ[A]
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(q : ℤ)) →ₗ[A]
        (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ)) :=
  ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent A S r d q).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).hom.hom).compl₂
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).hom.hom

/-- 同じ係数基底・同じ正規化生成元上の切断和（BF §2.2.6）。 -/
lemma positiveComponent_generator (S : SSet.{0}) {r d q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent A S r d q
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) d (ULift.up u)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S u x := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent A S r d q
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).toLinearEquiv
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).toLinearEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) d (ULift.up u))))
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).toLinearEquiv
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).toLinearEquiv.symm (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A S q x))) = _
  simp only [LinearEquiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent_gen A S _ x).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_value A S u x)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
