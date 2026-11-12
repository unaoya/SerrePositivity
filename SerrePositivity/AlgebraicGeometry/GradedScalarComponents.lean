module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousAway
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.GradedMulAction

/-!
概要：同じ次数の carrier を、指定した基底環の部分加群として扱う。
方針：Submodule.ofClass で scalar を指定し、恒等の graded RingHom で斉次局所化を比較する。
規約：元の grading の carrier の型 σ を変えたことを隠さない。
使われ方：動く基底の各段を共通の基底環に制限し、実際の Proj の切断と比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory HomogeneousLocalization
universe u v
variable {R S : Type u} {σ : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [SetLike σ S] [AddSubgroupClass σ S] [SMulMemClass σ R S]
variable (G : ℕ → σ) [GradedRing G]

/-- 元の次数の carrier を、指定した基底環上の部分加群として扱う。 -/
def gradedScalarComponents (n : ℕ) : Submodule R S := Submodule.ofClass (G n)

/-- scalar を指定し直しても、各次数の所属の条件は変わらない。 -/
theorem mem_gradedScalarComponents (n : ℕ) (x : S) :
    x ∈ gradedScalarComponents (R := R) G n ↔ x ∈ G n := Iff.rfl

/-- scalar を指定し直した次数成分は、同じ分解を持つ次数付き環になる。 -/
instance gradedScalarComponentsGradedRing : GradedRing (gradedScalarComponents (R := R) G) where
  one_mem := SetLike.one_mem_graded G
  mul_mem := by
    intro i j a b ha hb
    exact SetLike.mul_mem_graded (A := G) ha hb
  decompose' := DirectSum.Decomposition.decompose' (ℳ := G)
  left_inv := DirectSum.Decomposition.left_inv (ℳ := G)
  right_inv := DirectSum.Decomposition.right_inv (ℳ := G)

/-- scalar を指定した次数付き環から、元の次数付き環への恒等写像。 -/
def gradedScalarToOriginal : gradedScalarComponents (R := R) G →+*ᵍ G where
  toRingHom := RingHom.id S
  map_mem := fun h ↦ h

/-- 元の次数付き環から、scalar を指定した次数付き環への恒等写像。 -/
def gradedOriginalToScalar : G →+*ᵍ gradedScalarComponents (R := R) G where
  toRingHom := RingHom.id S
  map_mem := fun h ↦ h

/-- 同じ carrier を持つ二つの grading の斉次局所化は、環として自然に同型。 -/
def gradedScalarAwayIso (s : S) :
    CommRingCat.of (Away (gradedScalarComponents (R := R) G) s) ≅ CommRingCat.of (Away G s) where
  hom := CommRingCat.ofHom (HomogeneousLocalization.map (P := Submonoid.powers s) (Q := Submonoid.powers s)
      (gradedScalarToOriginal (R := R) G) le_rfl)
  inv := CommRingCat.ofHom (HomogeneousLocalization.map (P := Submonoid.powers s) (Q := Submonoid.powers s)
      (gradedOriginalToScalar (R := R) G) le_rfl)
  hom_inv_id := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
    rfl
  inv_hom_id := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
    rfl

/-- 二つの grading の比較は、周囲の通常の局所化の値を保つ。 -/
theorem gradedScalarAwayIso_val (s : S) (z : Away (gradedScalarComponents (R := R) G) s) :
    ((gradedScalarAwayIso (R := R) G s).hom.hom z).val = z.val := by
  change (HomogeneousLocalization.map (P := Submonoid.powers s) (Q := Submonoid.powers s)
      (gradedScalarToOriginal (R := R) G) le_rfl z).val = z.val
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rfl

/-- carrier の比較は、標準開を狭める斉次局所化の制限と可換。 -/
theorem gradedScalarAwayIso_awayMap {s t a : S} {d : ℕ}
    (ha : a ∈ G d) (ht : t = s * a)
    (z : Away (gradedScalarComponents (R := R) G) s) :
    (gradedScalarAwayIso (R := R) G t).hom.hom
        (HomogeneousLocalization.awayMap (gradedScalarComponents (R := R) G) ha ht z) =
      HomogeneousLocalization.awayMap G ha ht ((gradedScalarAwayIso (R := R) G s).hom.hom z) := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers t)
  rw [gradedScalarAwayIso_val, HomogeneousLocalization.val_awayMap,
    HomogeneousLocalization.val_awayMap, gradedScalarAwayIso_val]

/-- generic な grading の斉次局所化の R 加群構造。通常の局所化への単射で移す。 -/
@[instance_reducible]
def gradedOriginalAwayModule (s : S) : Module R (Away G s) :=
  Function.Injective.module R
    { toFun := HomogeneousLocalization.val
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
    (HomogeneousLocalization.val_injective (Submonoid.powers s))
    (HomogeneousLocalization.val_smul (Submonoid.powers s))

local instance gradedOriginalAwayLocalModule (s : S) : Module R (Away G s) := gradedOriginalAwayModule (R := R) G s
local instance gradedScalarAwayLocalModule (s : S) : Module R (Away (gradedScalarComponents (R := R) G) s) :=
  projectiveHomogeneousAwayModule (gradedScalarComponents (R := R) G) s

/-- 同じ grading の carrier の比較は、指定した基底環上でも線形。 -/
def gradedScalarAwayLinearEquiv (s : S) :
    Away (gradedScalarComponents (R := R) G) s ≃ₗ[R] Away G s :=
  { (gradedScalarAwayIso (R := R) G s).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := by
      intro r z
      apply HomogeneousLocalization.val_injective (Submonoid.powers s)
      change ((gradedScalarAwayIso (R := R) G s).hom.hom (r • z)).val =
        (r • (gradedScalarAwayIso (R := R) G s).hom.hom z).val
      rw [gradedScalarAwayIso_val, HomogeneousLocalization.val_smul,
        HomogeneousLocalization.val_smul, gradedScalarAwayIso_val] }

section Action
variable {P : Type u} [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
variable (B : ℕ → Submodule R P) [SetLike.GradedSMul B G]

/-- 係数環を明示した carrier 上にも、同じ次数付き作用がある。 -/
instance gradedScalarComponentsGradedSMul :
    SetLike.GradedSMul B (gradedScalarComponents (R := R) G) where
  smul_mem := by
    intro i j a x ha hx
    exact SetLike.GradedSMul.smul_mem (A := B) (B := G) ha hx
end Action

section SubmoduleRestriction
variable {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra R' S]
variable [IsScalarTower R R' S]

/-- 大きい基底環の部分加群は、共通の小さい基底環の作用でも閉じる。 -/
theorem gradedSubmoduleScalarRestrictionMemClass : SMulMemClass (Submodule R' S) R S where
  smul_mem {s} r _ hx := s.smul_of_tower_mem r hx
end SubmoduleRestriction

end SerrePositivity.AlgebraicGeometry
