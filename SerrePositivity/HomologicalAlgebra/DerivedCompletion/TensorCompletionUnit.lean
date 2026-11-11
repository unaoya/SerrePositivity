module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
public import Mathlib.RingTheory.TensorProduct.Maps
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 完備テンソル内の主完備化単位

## 概要
通常テンソルの一方を先に主完備化しても、最後に p 完備化した環は変わらない。

## 方針
完備化単位のテンソルが誘導する射を固定する。逆射を主完備化の普遍性で延長し、
二つの合成をテンソルの生成元と完備化単位上で照合する。

## 規約
平坦性・正則性・有限性は仮定しない。各標準脚の式を保つ。

## 使われ方
BS 著者版 Theorem 6.4 の小さい分冪模型の各項の完備係数変更。
-/

public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace SerrePositivity.DerivedCompletion.TensorCompletionUnit

set_option backward.isDefEq.respectTransparency false

private def unitAlg (p : ℕ) (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] :
    R →ₐ[k] CompletedRing p R :=
  ⟨(principalCompletionRingCatUnit p (CommRingCat.of R)).hom, fun _ => rfl⟩

private theorem targetComplete (p : ℕ) (R T : Type u) [CommRing R] [CommRing T]
    (f : R →+* CompletedRing p T) :
    let := f.toAlgebra
    IsModuleComplete R (p : R) (ModuleCat.of R (CompletedRing p T)) := by
  let := f.toAlgebra
  let := principalCompletionCommRing T (p : T)
  apply (isModuleComplete_algebraMap_iff R (CompletedRing p T) (p : R) (CompletedRing p T)).mp
  change IsModuleComplete (CompletedRing p T) (f (p : R)) _
  have hp : f (p : R) = principalCompletionUnitRingHom T (p : T) (p : T) :=
    (map_natCast f p).trans (map_natCast (principalCompletionUnitRingHom T (p : T)) p).symm
  rw [hp]
  have H := principalCompletion_isModuleComplete_unit (p : T)
  rw [isModuleComplete_iff_recurrence_bijective] at H ⊢
  exact H

/-- 元の代数射が主完備環の間に誘導する標準の代数射。 -/
def completedAlgMap (p : ℕ) (k R S : Type u) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) :
    CompletedRing p R →ₐ[k] CompletedRing p S := by
  refine ⟨((principalCompletionRingFunctor p).map (CommRingCat.ofHom f.toRingHom)).hom, ?_⟩
  intro a
  change ((principalCompletionRingFunctor p).map (CommRingCat.ofHom f.toRingHom)).hom
    (principalCompletionRingCatUnit p (CommRingCat.of R) (algebraMap k R a)) =
      principalCompletionRingCatUnit p (CommRingCat.of S) (algebraMap k S a)
  exact (ConcreteCategory.congr_hom
    (ringCatMap_comp_unit p (CommRingCat.ofHom f.toRingHom)) (algebraMap k R a)).trans
    (congrArg (principalCompletionRingCatUnit p (CommRingCat.of S)) (f.commutes a))

/-- 主完備環の標準代数射は完備化単位と可換。 -/
theorem completedAlgMap_unit (p : ℕ) (k R S : Type u) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (x : R) :
    completedAlgMap p k R S f (principalCompletionRingCatUnit p (CommRingCat.of R) x) =
      principalCompletionRingCatUnit p (CommRingCat.of S) (f x) :=
  ConcreteCategory.congr_hom (ringCatMap_comp_unit p (CommRingCat.ofHom f.toRingHom)) x

variable (p : ℕ) (k B R : Type u) [CommRing k] [CommRing B] [CommRing R]
variable [Algebra k B] [Algebra k R]

local notation "T0" => B ⊗[k] R
local notation "T1" => B ⊗[k] CompletedRing p R
local notation "jR" => CommRingCat.Hom.hom (principalCompletionRingCatUnit p (CommRingCat.of R))
local notation "j0" => CommRingCat.Hom.hom (principalCompletionRingCatUnit p (CommRingCat.of T0))
local notation "j1" => CommRingCat.Hom.hom (principalCompletionRingCatUnit p (CommRingCat.of T1))

/-- 片方の完備化単位を通常テンソルした標準の代数射。 -/
def completedTensorUnitMap : T0 →ₐ[B] T1 :=
  Algebra.TensorProduct.map (AlgHom.id B B) (unitAlg p k R)

private def rightComplete : CompletedRing p R →+* CompletedRing p T0 :=
  ((principalCompletionRingFunctor p).map
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : R →+* T0))).hom

private theorem rightComplete_unit (r : R) :
    rightComplete p k B R ((jR) r) = (j0) (1 ⊗ₜ[k] r) :=
  ConcreteCategory.congr_hom (ringCatMap_comp_unit p
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : R →+* T0))) r

private def rightCompleteAlg : CompletedRing p R →ₐ[k] CompletedRing p T0 :=
  ⟨rightComplete p k B R, fun a => by
    change rightComplete p k B R ((jR) (algebraMap k R a)) = (j0) (algebraMap k T0 a)
    rw [rightComplete_unit]
    exact congrArg (j0) ((Algebra.TensorProduct.includeRight : R →ₐ[k] T0).commutes a)⟩

private def tensorLift : T1 →ₐ[k] CompletedRing p T0 :=
  Algebra.TensorProduct.lift
    ((unitAlg p k T0).comp (Algebra.TensorProduct.includeLeft : B →ₐ[k] T0))
    (rightCompleteAlg p k B R) (fun _ _ => Commute.all _ _)

private def forward : CompletedRing p T0 →+* CompletedRing p T1 :=
  ((principalCompletionRingFunctor p).map
    (CommRingCat.ofHom (completedTensorUnitMap p k B R).toRingHom)).hom

private theorem forward_unit (z : T0) :
    forward p k B R ((j0) z) = (j1) (completedTensorUnitMap p k B R z) :=
  ConcreteCategory.congr_hom (ringCatMap_comp_unit p
    (CommRingCat.ofHom (completedTensorUnitMap p k B R).toRingHom)) z

private def backward : CompletedRing p T1 →+* CompletedRing p T0 :=
  principalCompletionLift T1 (p : T1) (CompletedRing p T0) (tensorLift p k B R).toRingHom
    (targetComplete p T1 T0 (tensorLift p k B R).toRingHom)

private theorem backward_unit (z : T1) :
    backward p k B R ((j1) z) = tensorLift p k B R z :=
  RingHom.congr_fun (principalCompletionLift_comp T1 (p : T1) (CompletedRing p T0)
    (tensorLift p k B R).toRingHom (targetComplete p T1 T0 (tensorLift p k B R).toRingHom)) z

private theorem tensorLift_unit (z : T0) :
    tensorLift p k B R (completedTensorUnitMap p k B R z) = (j0) z := by
  induction z using TensorProduct.inductionOn with
  | tmul b r =>
    simp only [completedTensorUnitMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      tensorLift, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
    change (j0) (b ⊗ₜ[k] 1) * rightComplete p k B R ((jR) r) = (j0) (b ⊗ₜ[k] r)
    rw [rightComplete_unit, ← map_mul]
    congr 1
    simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem backward_forward :
    (backward p k B R).comp (forward p k B R) = RingHom.id (CompletedRing p T0) := by
  apply (principalCompletion_existsUnique_ringHom T0 (p : T0) (CompletedRing p T0) (j0)
    (targetComplete p T0 T0 (j0))).unique
  · apply RingHom.ext
    intro z
    change backward p k B R (forward p k B R ((j0) z)) = (j0) z
    rw [forward_unit, backward_unit, tensorLift_unit]
  · rfl

private theorem forward_rightComplete :
    (forward p k B R).comp (rightComplete p k B R) =
      (j1).comp (Algebra.TensorProduct.includeRight.toRingHom : CompletedRing p R →+* T1) := by
  let b := ((j1).comp
    (Algebra.TensorProduct.includeRight.toRingHom : CompletedRing p R →+* T1)).comp (jR)
  apply (principalCompletion_existsUnique_ringHom R (p : R) (CompletedRing p T1) b
    (targetComplete p R T1 b)).unique
  · apply RingHom.ext
    intro r
    change forward p k B R (rightComplete p k B R ((jR) r)) = (j1) (1 ⊗ₜ[k] (jR) r)
    rw [rightComplete_unit, forward_unit]
    simp only [completedTensorUnitMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  · rfl

private theorem forward_backward :
    (forward p k B R).comp (backward p k B R) = RingHom.id (CompletedRing p T1) := by
  apply (principalCompletion_existsUnique_ringHom T1 (p : T1) (CompletedRing p T1) (j1)
    (targetComplete p T1 T1 (j1))).unique
  · apply RingHom.ext
    intro z
    change forward p k B R (backward p k B R ((j1) z)) = (j1) z
    rw [backward_unit]
    induction z using TensorProduct.inductionOn with
    | tmul b r =>
      simp only [tensorLift, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
      change forward p k B R ((j0) (b ⊗ₜ[k] 1) * rightComplete p k B R r) = (j1) (b ⊗ₜ[k] r)
      rw [map_mul, forward_unit]
      have hr := RingHom.congr_fun (forward_rightComplete p k B R) r
      change forward p k B R (rightComplete p k B R r) = (j1) (1 ⊗ₜ[k] r) at hr
      rw [hr]
      simp only [completedTensorUnitMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      rw [← map_mul]
      congr 1
      simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · rfl

/-- テンソルの一方への完備化単位は、全体の主完備化後に標準の環同型を誘導する。 -/
def completionTensorUnitEquiv : CompletedRing p T0 ≃+* CompletedRing p T1 :=
  RingEquiv.ofRingHom (forward p k B R) (backward p k B R)
    (forward_backward p k B R) (backward_forward p k B R)

/-- 環同型は、もとのテンソルの各標準元を指定された単位へ送る。 -/
theorem completionTensorUnitEquiv_unit (z : T0) :
    completionTensorUnitEquiv p k B R ((j0) z) =
      (j1) (completedTensorUnitMap p k B R z) :=
  forward_unit p k B R z

/-- テンソル内の完備化単位の同型は、左係数を保つ。 -/
theorem completionTensorUnitEquiv_base (b : B) :
    completionTensorUnitEquiv p k B R (algebraMap B (CompletedRing p T0) b) =
      algebraMap B (CompletedRing p T1) b := by
  change completionTensorUnitEquiv p k B R ((j0) (b ⊗ₜ[k] 1)) = (j1) (b ⊗ₜ[k] 1)
  rw [completionTensorUnitEquiv_unit]
  simp only [completedTensorUnitMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

/-- テンソル内の完備化単位の環同型を、左係数上の代数同型として読む。 -/
def completionTensorUnitAlgEquiv : CompletedRing p T0 ≃ₐ[B] CompletedRing p T1 :=
  { completionTensorUnitEquiv p k B R with
    commutes' := completionTensorUnitEquiv_base p k B R }

variable {R} {S : Type u} [CommRing S] [Algebra k S]

/-- テンソル内の完備化単位の同型は、元の代数射について厳密に自然。 -/
theorem completionTensorUnitAlgEquiv_naturality (f : R →ₐ[k] S) :
    (completionTensorUnitAlgEquiv p k B S).toAlgHom.comp
        (completedAlgMap p B (B ⊗[k] R) (B ⊗[k] S)
          (Algebra.TensorProduct.map (AlgHom.id B B) f)) =
      (completedAlgMap p B (B ⊗[k] CompletedRing p R) (B ⊗[k] CompletedRing p S)
        (Algebra.TensorProduct.map (AlgHom.id B B) (completedAlgMap p k R S f))).comp
          (completionTensorUnitAlgEquiv p k B R).toAlgHom := by
  apply AlgHom.toLinearMap_injective
  apply principalCompletionLinearMap_ext B p
    (completedRing_isModuleComplete B p (A := B ⊗[k] CompletedRing p S))
  intro z
  change completionTensorUnitEquiv p k B S
      (completedAlgMap p B (B ⊗[k] R) (B ⊗[k] S)
        (Algebra.TensorProduct.map (AlgHom.id B B) f) ((j0) z)) =
    completedAlgMap p B (B ⊗[k] CompletedRing p R) (B ⊗[k] CompletedRing p S)
      (Algebra.TensorProduct.map (AlgHom.id B B) (completedAlgMap p k R S f))
        (completionTensorUnitEquiv p k B R ((j0) z))
  rw [completedAlgMap_unit, completionTensorUnitEquiv_unit, completionTensorUnitEquiv_unit,
    completedAlgMap_unit]
  induction z using TensorProduct.inductionOn with
  | tmul b r =>
    simp only [completedTensorUnitMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[k] CompletedRing p S))
        (b ⊗ₜ[k] principalCompletionRingCatUnit p (CommRingCat.of S) (f r)) =
      principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[k] CompletedRing p S))
        (b ⊗ₜ[k] completedAlgMap p k R S f ((jR) r))
    rw [completedAlgMap_unit]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end SerrePositivity.DerivedCompletion.TensorCompletionUnit
