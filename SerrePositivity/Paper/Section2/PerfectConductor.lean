module

public import SerrePositivity.CommutativeAlgebra.RootTower.PerfectConductor

/-!
# 論文の等標数の設定での共通分母

正則な完備局所環 `A` 上の有限拡大 `D` で、perfection 全体に共通の非零分母を構成する。
基底の正規性（正則局所環の正規性）と剰余体の完全性をここで供給し、
一般論 `exists_tower_perfection_conductor_of_normal_base`（CommutativeAlgebra/RootTower/PerfectConductor）を適用する。
-/

public section
universe u
namespace SerrePositivity.Section2

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]

attribute [local instance] towerPerfectionAlgebra

/-- 論文の等標数の設定から、perfection 全体に共通の非零分母を構成する。
正則基底の正規性と剰余体の完全性を証明内で供給し、追加の仮定にはしない。
基底の正規性は証明済みの正則パラメータから導かれる。 -/
theorem exists_tower_perfection_conductor
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsDomain D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    [Algebra A (PerfectClosure D p)]
    [CharP (IsLocalRing.ResidueField D) p] [PerfectField (IsLocalRing.ResidueField D)]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap A D)))
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) :
    ∃ g : A, g ≠ 0 ∧ ∀ c : PerfectClosure D p,
      PerfectClosure.of D p (algebraMap A D g) * c ∈
        perfectionApproximation D p (Tower A t p) 0 := by
  let := isIntegrallyClosed_of_isRegularLocalRing A
  let er := residueFieldEquiv_of_surjective (R := A) D hres
  let : CharP (IsLocalRing.ResidueField A) p := er.toRingHom.charP er.injective p
  let : PerfectField (IsLocalRing.ResidueField A) := PerfectField.of_ringEquiv er.symm
  exact exists_tower_perfection_conductor_of_normal_base D p A t ht hdim hinj hbase hsep

end SerrePositivity.Section2
