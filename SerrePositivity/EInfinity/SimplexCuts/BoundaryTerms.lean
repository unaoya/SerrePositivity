module

public import SerrePositivity.EInfinity.SimplexCuts.OutputBoundaryTerms
public import SerrePositivity.EInfinity.Surjection.DeletionSigns
public import SerrePositivity.EInfinity.Surjection.Deletion

/-!
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
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 入力単体の境界に由来する項。Leibnizの右辺を移項した負号を含む。 -/
def simplexBoundaryTerm (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) d) : (q : ℕ) → SimplexBoundaryIndex r d q →
      S _⦋q⦌ → (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _, _ => 0
  | q + 1, ⟨i, s⟩, x => by
    have h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) =
        -((d + (q + 1) : ℕ) : ℤ) + 1 := by omega
    exact -((-1 : ℤ)^(d + i.val)) •
      (eqToHom (congrArg (fun t : ℤ => (power (chains A S) (r + 1)).X t) h)).hom
        (cutTerm A S s (positiveWord u) (S.δ i x))

/-- 係数語の境界に由来する項。非全射・隣接退化の削除は零にする。 -/
def coefficientBoundaryTerm (S : SSet.{0}) (r : ℕ) : (d q : ℕ) →
    Surjection.BasisWord (r + 1) d → CoefficientBoundaryIndex r d q →
      S _⦋q⦌ → (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _, _, _, _ => 0
  | d + 1, q, u, ⟨j, s⟩, x => by
    let v : Surjection.Word (r + 1) (r + d + 2) :=
      Eq.mp (congrArg (fun l => Surjection.Word (r + 1) l)
        (show (r + 1) + (d + 1) = r + d + 2 by omega)) u
    let k : Fin (r + d + 2) := Fin.cast (by omega) j
    let w : Fin (r + d + 1) → Fin (r + 1) := Surjection.erase v.val k
    exact if hw : Function.Surjective w ∧ Surjection.Nondegenerate w then by
      let s' : Cut (r + d) q :=
        Eq.mp (congrArg (fun m => Cut m q) (show r + (d + 1) - 1 = r + d by omega)) s
      have h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) =
          -(((d + 1) + q : ℕ) : ℤ) + 1 := by omega
      exact -Surjection.deletionCoefficient v.val k •
        (eqToHom (congrArg (fun t : ℤ => (power (chains A S) (r + 1)).X t) h)).hom
          (cutTerm A S s' ⟨w, hw⟩ x)
    else 0

/-- L09a の同じ値域に集めた全境界項。固定点で零となる項も除かない。 -/
def boundaryBalanceTerm (S : SSet.{0}) {r d : ℕ} (u : Surjection.BasisWord (r + 1) d)
    (q : ℕ) : BoundaryBalanceIndex u q → S _⦋q⦌ →
      (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | .inl ⟨s, a, j⟩, x => by
    have h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 =
        -((d + q : ℕ) : ℤ) + 1 := by omega
    exact (eqToHom (congrArg (fun t : ℤ => (power (chains A S) (r + 1)).X t) h)).hom
      (outputBoundaryTerm A S s (positiveWord u) a j x)
  | .inr (.inl i), x => coefficientBoundaryTerm A S r d q u i x
  | .inr (.inr i), x => simplexBoundaryTerm A S u q i x

end SerrePositivity.EInfinity.SimplexCuts
