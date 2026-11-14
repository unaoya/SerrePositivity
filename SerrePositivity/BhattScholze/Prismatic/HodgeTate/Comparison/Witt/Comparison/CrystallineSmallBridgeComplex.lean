module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineBridgeAlgebra
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineBridgeAlgebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 小さい結晶の橋の線形複体

## 概要
整係数の小さい結晶の橋から、基底線形な交代余面複体の射を取り出す。
始域と終域の整数添字の複体は導来 p 完備である。

## 方針
既存の台加群の構成と橋の基底線形性を使い、項ごとの完備性を零延長に移す。

## 規約
係数環は既存の結晶基底 ℤ_p。

## 使われ方
BS 著者版 Theorem 6.4 の mod p の比較を整係数の比較へ持ち上げる。
-/

public noncomputable section

open CategoryTheory HomologicalComplex AlgebraicTopology SerrePositivity.Cosimplicial
open SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "k" => crystallineBase p
local notation "Z" => crystallineBasePrism p
local notation "hZ" => crystallineBaseBounded p
local notation "ιX" => htBase Z hZ r
local notation "ιY" => pdCechBase p k r

private theorem smallBridge_base_comm :
    htBase (crystallineBasePrism.{u} p) hZ r ≫ crystallineSmallBridge.{u} p r =
      pdCechBase p (crystallineBase.{u} p) r := by
  rw [← crystallineSmallBridgeAlgebra_forget]
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  exact Under.w ((crystallineSmallBridgeAlgebra.{u} p r).app ⦋n⦌)

/-- affine 側の交代余面複体を結晶基底上の加群として読む。 -/
def crystallineSmallSourceComplex : CochainComplex (ModuleCat.{u} (crystallineBase.{u} p)) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat k)).obj (toModules k (zpCech p r) (ιX))

/-- 小さい分冪側の交代余面複体を結晶基底上の加群として読む。 -/
def crystallineSmallTargetComplex : CochainComplex (ModuleCat.{u} (crystallineBase.{u} p)) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat k)).obj (toModules k (pdRings p r) (ιY))

/-- 整係数の小さい結晶の橋が誘導する基底線形な余鎖写像。 -/
def crystallineSmallBridgeCochainMap :
    crystallineSmallSourceComplex.{u} p r ⟶ crystallineSmallTargetComplex.{u} p r :=
  moduleCochainMap k (ιX) (ιY) (crystallineSmallBridge p r) (smallBridge_base_comm p r)

private theorem source_terms_complete (n : ℕ) :
    IsModuleComplete k (p : k) ((crystallineSmallSourceComplex.{u} p r).X n) := by
  let S := (zpCech.{u} p r).obj ⦋n⦌
  let : Algebra (crystallineBase.{u} p) S :=
    ((htBase (crystallineBasePrism.{u} p) hZ r).app ⦋n⦌).hom.toAlgebra
  change IsModuleComplete (crystallineBase.{u} p) (p : crystallineBase.{u} p)
    (ModuleCat.of (crystallineBase.{u} p) S)
  apply (isModuleComplete_algebraMap_iff (crystallineBase.{u} p) S
    (p : crystallineBase.{u} p) S).mp
  rw [map_natCast (algebraMap (crystallineBase.{u} p) S)]
  change IsModuleComplete (aff.{u} p r ⦋n⦌).X.B
    (p : (aff.{u} p r ⦋n⦌).X.B) (ModuleCat.of _ (aff.{u} p r ⦋n⦌).X.B)
  exact (aff.{u} p r ⦋n⦌).X.Q.complete_p

private theorem target_terms_complete (n : ℕ) :
    IsModuleComplete k (p : k) ((crystallineSmallTargetComplex.{u} p r).X n) := by
  change IsModuleComplete (crystallineBase.{u} p) (p : crystallineBase.{u} p)
    (ModuleCat.of (crystallineBase.{u} p) (pdTerm p (crystallineBase.{u} p) r n))
  exact completedRing_isModuleComplete (crystallineBase.{u} p) p
    (A := pdRaw (crystallineBase.{u} p) r n)

private theorem extended_complete
    (K : CochainComplex (ModuleCat.{u} (crystallineBase.{u} p)) ℕ)
    (hK : ∀ n, IsModuleComplete k (p : k) (K.X n)) :
    IsComplete k (p : k) (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat)) := by
  apply isComplete_Q_of_terms k (p : k)
  intro i
  let emb := ComplexShape.embeddingUpNat
  by_cases h : ∃ j, emb.f j = i
  · obtain ⟨j, rfl⟩ := h
    exact isModuleComplete_of_linearEquiv k (p : k) _ _
      (K.extendXIso emb rfl).symm.toLinearEquiv (hK j)
  · have hz := K.isZero_extend_X emb i (fun j hj => h ⟨j, hj⟩)
    let : Subsingleton ((K.extend emb).X i) := ModuleCat.isZero_iff_subsingleton.mp hz
    exact isModuleComplete_of_pow_smul_zero k (p : k) _ 0
      (fun _ => Subsingleton.elim _ _)

/-- 結晶の affine 複体の整数添字への零延長は導来 p 完備。 -/
theorem crystallineSmallSourceComplex_isComplete :
    IsComplete (crystallineBase.{u} p) (p : crystallineBase.{u} p)
      (DerivedCategory.Q.obj
        ((crystallineSmallSourceComplex.{u} p r).extend ComplexShape.embeddingUpNat)) :=
  extended_complete p (crystallineSmallSourceComplex p r) (source_terms_complete p r)

/-- 小さい分冪複体の整数添字への零延長は導来 p 完備。 -/
theorem crystallineSmallTargetComplex_isComplete :
    IsComplete (crystallineBase.{u} p) (p : crystallineBase.{u} p)
      (DerivedCategory.Q.obj
        ((crystallineSmallTargetComplex.{u} p r).extend ComplexShape.embeddingUpNat)) :=
  extended_complete p (crystallineSmallTargetComplex p r) (target_terms_complete p r)

end SerrePositivity.BhattScholze.Prismatic
