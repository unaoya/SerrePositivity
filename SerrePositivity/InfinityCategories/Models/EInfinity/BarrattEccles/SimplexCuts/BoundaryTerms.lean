module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OutputBoundaryTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Deletion

/-!
模型。文献の定義との比較は後で
# 一般の BF 切断微分の符号付き全項

Berger–Fresse §2.2.6–7、M14 L09a。
出力面を正、係数の微分と入力の微分を負として、同じ全次数へ移送する。
零次数の境界、退化した語、退化した切断も零の項として保持する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 入力単体の境界に由来する項。Leibnizの右辺を移項した負号を含む。 -/
def simplexBoundaryTerm (S : SSet.{0}) {r d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) : (q : ℕ) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SimplexBoundaryIndex r d q →
      S _⦋q⦌ → (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _, _ => 0
  | q + 1, ⟨i, s⟩, x => by
    have h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) =
        -((d + (q + 1) : ℕ) : ℤ) + 1 := by omega
    exact -((-1 : ℤ)^(d + i.val)) •
      (eqToHom (congrArg (fun t : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X t) h)).hom
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) (S.δ i x))

/-- 係数語の境界に由来する項。非全射・隣接退化の削除は零にする。 -/
def coefficientBoundaryTerm (S : SSet.{0}) (r : ℕ) : (d q : ℕ) →
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientBoundaryIndex r d q →
      S _⦋q⦌ → (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _, _, _, _ => 0
  | d + 1, q, u, ⟨j, s⟩, x => by
    let v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (r + d + 2) :=
      Eq.mp (congrArg (fun l => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) l)
        (show (r + 1) + (d + 1) = r + d + 2 by omega)) u
    let k : Fin (r + d + 2) := Fin.cast (by omega) j
    let w : Fin (r + d + 1) → Fin (r + 1) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val k
    exact if hw : Function.Surjective w ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate w then by
      let s' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q :=
        Eq.mp (congrArg (fun m => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (show r + (d + 1) - 1 = r + d by omega)) s
      have h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) =
          -(((d + 1) + q : ℕ) : ℤ) + 1 := by omega
      exact -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val k •
        (eqToHom (congrArg (fun t : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X t) h)).hom
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S s' ⟨w, hw⟩ x)
    else 0

/-- L09a の同じ値域に集めた全境界項。固定点で零となる項も除かない。 -/
def boundaryBalanceTerm (S : SSet.{0}) {r d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d)
    (q : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex u q → S _⦋q⦌ →
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | .inl ⟨s, a, j⟩, x => by
    have h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 =
        -((d + q : ℕ) : ℤ) + 1 := by omega
    exact (eqToHom (congrArg (fun t : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X t) h)).hom
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) a j x)
  | .inr (.inl i), x => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r d q u i x
  | .inr (.inr i), x => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm A S u q i x

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
