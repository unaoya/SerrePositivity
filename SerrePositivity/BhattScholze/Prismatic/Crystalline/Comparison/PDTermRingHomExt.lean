module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawRingHomExt
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermReductionLinear
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermReductionLinear
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech

/-!
# 完備分冪項からの環射の一意性

## 概要
p 正則で p 局所な完備標的への代数射は、頂点の初期座標の像で決まる。

## 方針
未完備の分冪模型で環射を比較し、主完備化の一意延長を適用する。

## 規約
標的の p 完備性は加群の導来完備性として明記する。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の小さい結晶比較の射を追跡する。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] {k T : Type u} [CommRing k] [CommRing T] [Algebra k T]
variable (r n : ℕ) (hreg : Function.Injective (fun x : T => (p : T) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : T))
variable (hcomplete : IsModuleComplete T (p : T) (ModuleCat.of T T))
variable (f g : pdTerm p k r n →ₐ[k] T)
variable (hv : ∀ j : Fin r, ∀ i : Fin (n + 1),
  f (pdTermCompletionUnitAlg p k r n (PDSmallRawEnvelope.unit r n
    (MvPolynomial.X (ULift.up j, i)))) =
  g (pdTermCompletionUnitAlg p k r n (PDSmallRawEnvelope.unit r n
    (MvPolynomial.X (ULift.up j, i)))))

include hreg hlocal hcomplete hv in
private theorem complete_ext : f = g := by
  let η := pdTermCompletionUnitAlg p k r n
  have hraw : f.comp η = g.comp η :=
    pdRawAlgHom_ext_of_primeRegular p r n hreg hlocal (f.comp η) (g.comp η) hv
  let R := pdRaw k r n
  let b := g.toRingHom.comp (principalCompletionUnitRingHom R (p : R))
  let := b.toAlgebra
  have hT : IsModuleComplete R (p : R) (ModuleCat.of R T) := by
    apply (isModuleComplete_algebraMap_iff R T (p : R) T).mp
    change IsModuleComplete T (b (p : R)) (ModuleCat.of T T)
    rw [map_natCast b]
    exact hcomplete
  have H := principalCompletion_existsUnique_ringHom R (p : R) T b hT
  apply AlgHom.toRingHom_injective
  apply H.unique
  · exact congrArg AlgHom.toRingHom hraw
  · rfl

include hreg hlocal hcomplete hv

/-- p 正則で p 局所な完備標的への二つの代数射は、各頂点の初期座標で比較できる。 -/
theorem pdTermAlgHom_ext_of_primeRegular : f = g :=
  complete_ext p r n hreg hlocal hcomplete f g hv

end SerrePositivity.BhattScholze.Prismatic
