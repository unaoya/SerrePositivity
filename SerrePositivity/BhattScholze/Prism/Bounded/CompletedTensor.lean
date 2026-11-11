module

public import SerrePositivity.BhattScholze.Delta.Basic.Tensor
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation

/-!
# 完備 δ 環のテンソル押し出し

## 概要
通常の δ テンソル積を二元で完備化した環の普遍性。

## 方針
通常のテンソル積と実導来完備化 H⁰ の δ 射の一意延長を合成する。

## 規約
完備化の第二座標は左因子の prism 生成元の像。

## 使われ方
BS 著者版 Corollary 3.12 と Proposition 3.13 (2)。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze

open DerivedCompletion
open scoped TensorProduct
open Algebra.TensorProduct

namespace OrientedPrism.Hom

variable {p : ℕ} [Fact p.Prime]
variable {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- prism 射は生成元を終域の生成元の単元倍へ送る（BS 著者版 Lemma 3.5）。 -/
theorem map_generator_unit_mul (f : Hom P Q) :
    ∃ r : Bˣ, f.toRingHom P.generator = Q.generator * r := by
  obtain ⟨r, hr, he⟩ := f.map_delta.exists_isUnit_of_distinguished_of_mem_span
    P.isDistinguished_generator f.map_generator_mem Q.generator_mem_jacobson Q.p_mem_jacobson
  exact ⟨hr.unit, by rw [hr.unit_spec]; exact he⟩

end OrientedPrism.Hom

section CompletedTensor

variable {p : ℕ} [Fact p.Prime]
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] (Q : OrientedPrism p B)

local notation "U" => B ⊗[A] C
local notation "l" => (includeLeftRingHom : B →+* U)
local notation "r" => (includeRight.toRingHom : C →+* U)
local notation "d" => (l Q.generator)

/-- 完備テンソル積の台環（BS 著者版 Corollary 3.12）。 -/
abbrev PrismCompletedTensor := PDCompletionH0 U p d

instance prismCompletedTensorCommRing : CommRing (PrismCompletedTensor (A := A) (C := C) Q) :=
  pdCompletionCommRing U p d

local notation "H" => PrismCompletedTensor (A := A) (C := C) Q
local notation "j" => pdCompletionUnit U p d

/-- 完備テンソル積への左脚。 -/
abbrev prismCompletedTensorLeft : B →+* H := (j).comp l

/-- 完備テンソル積への右脚。 -/
abbrev prismCompletedTensorRight : C →+* H := (j).comp r

/-- 完備テンソル積は p について導来完備。 -/
theorem prismCompletedTensor_complete_p :
    IsModuleComplete H (p : H) (ModuleCat.of H H) :=
  pdCompletionH0_self_complete_p U p d

/-- 完備テンソル積は左脚で写した生成元について導来完備。 -/
theorem prismCompletedTensor_complete_generator :
    IsModuleComplete H (prismCompletedTensorLeft Q Q.generator) (ModuleCat.of H H) :=
  pdCompletionH0_self_complete_d U p d

variable (D : DeltaStructure p A) (F : DeltaStructure p C)
variable (hQ : D.IsDeltaHom Q.deltaStructure (algebraMap A B))
variable (hF : D.IsDeltaHom F (algebraMap A C))

/-- 完備テンソル積の δ 構造。 -/
def prismCompletedTensorDelta : DeltaStructure p H :=
  deltaPDCompletionStructure (tensorDeltaStructure D Q.deltaStructure F hQ hF) d

/-- 左脚は δ 射。 -/
theorem prismCompletedTensorLeft_isDeltaHom :
    Q.deltaStructure.IsDeltaHom (prismCompletedTensorDelta Q D F hQ hF)
      (prismCompletedTensorLeft Q) :=
  (pdCompletionUnit_isDeltaHom (tensorDeltaStructure D Q.deltaStructure F hQ hF) d).comp
    (tensorDeltaStructure_includeLeft D Q.deltaStructure F hQ hF)

/-- 右脚は δ 射。 -/
theorem prismCompletedTensorRight_isDeltaHom :
    F.IsDeltaHom (prismCompletedTensorDelta Q D F hQ hF) (prismCompletedTensorRight Q) :=
  (pdCompletionUnit_isDeltaHom (tensorDeltaStructure D Q.deltaStructure F hQ hF) d).comp
    (tensorDeltaStructure_includeRight D Q.deltaStructure F hQ hF)

/-- 完備テンソル積の両脚は係数環上で一致する。 -/
theorem prismCompletedTensor_square :
    (prismCompletedTensorLeft Q (A := A) (C := C)).comp (algebraMap A B) =
      (prismCompletedTensorRight Q).comp (algebraMap A C) := by
  change ((j).comp l).comp (algebraMap A B) = ((j).comp r).comp (algebraMap A C)
  rw [RingHom.comp_assoc, RingHom.comp_assoc, includeLeftRingHom_comp_algebraMap]

/-- 概要：両脚に合う完備テンソル積からの δ 射は一意。
方針：未完備テンソル積の射を p と左脚の生成元について完備化する。
規約：BS 著者版 Corollary 3.12 と Proposition 3.13 (2) の普遍性。
使われ方：完備自由 δ 環の底変換。 -/
theorem existsUnique_prismCompletedTensorHom {T : Type u} [CommRing T]
    (G : DeltaStructure p T) (f : B →+* T) (g : C →+* T)
    (hf : Q.deltaStructure.IsDeltaHom G f) (hg : F.IsDeltaHom G g)
    (h : f.comp (algebraMap A B) = g.comp (algebraMap A C))
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (f Q.generator) (ModuleCat.of T T)) :
    ∃! k : H →+* T, (prismCompletedTensorDelta Q D F hQ hF).IsDeltaHom G k ∧
      k.comp (prismCompletedTensorLeft Q) = f ∧ k.comp (prismCompletedTensorRight Q) = g := by
  let E := tensorDeltaStructure D Q.deltaStructure F hQ hF
  obtain ⟨s, hs, hu⟩ := existsUnique_tensorDeltaHom D Q.deltaStructure F hQ hF G f g hf hg h
  have hsd : s d = f Q.generator := DFunLike.congr_fun hs.2.1 _
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaPDCompletionHom E d G s hs.1 hp (hsd ▸ hd)
  refine ⟨k, ⟨hk.1, ?_, ?_⟩, ?_⟩
  · change k.comp ((j).comp l) = f
    rw [← RingHom.comp_assoc, hk.2, hs.2.1]
  · change k.comp ((j).comp r) = g
    rw [← RingHom.comp_assoc, hk.2, hs.2.2]
  · intro k' hk'
    apply hku
    refine ⟨hk'.1, hu _ ⟨hk'.1.comp (pdCompletionUnit_isDeltaHom E d), ?_, ?_⟩⟩
    · rw [RingHom.comp_assoc]
      exact hk'.2.1
    · rw [RingHom.comp_assoc]
      exact hk'.2.2

/-- 完備テンソル積の二つの脚は任意の δ 射を決定する。 -/
theorem prismCompletedTensorHom_ext {T : Type u} [CommRing T]
    (G : DeltaStructure p T) {k k' : H →+* T}
    (hk : (prismCompletedTensorDelta Q D F hQ hF).IsDeltaHom G k)
    (hk' : (prismCompletedTensorDelta Q D F hQ hF).IsDeltaHom G k')
    (hl : k.comp (prismCompletedTensorLeft Q) = k'.comp (prismCompletedTensorLeft Q))
    (hr : k.comp (prismCompletedTensorRight Q) = k'.comp (prismCompletedTensorRight Q))
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (k' (prismCompletedTensorLeft Q Q.generator))
      (ModuleCat.of T T)) : k = k' := by
  let L := prismCompletedTensorLeft Q (A := A) (C := C)
  let R : C →+* H := prismCompletedTensorRight Q (A := A)
  have hw : (k'.comp L).comp (algebraMap A B) = (k'.comp R).comp (algebraMap A C) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    exact congrArg k'.comp (prismCompletedTensor_square Q)
  obtain ⟨_, _, hu⟩ := existsUnique_prismCompletedTensorHom Q D F hQ hF G
    (k'.comp L) (k'.comp R)
    (hk'.comp (prismCompletedTensorLeft_isDeltaHom Q D F hQ hF))
    (hk'.comp (prismCompletedTensorRight_isDeltaHom Q D F hQ hF)) hw hp hd
  exact (hu k ⟨hk, hl, hr⟩).trans (hu k' ⟨hk', rfl, rfl⟩).symm

/-- 概要：右因子の δ 同型は完備テンソル積の同型を誘導する。
方針：完備テンソル積の普遍性から両方向を延長する。
規約：BS 著者版 Proposition 3.13 (2) の同型の比較。
使われ方：選択した envelope と変数模型を取り替える。 -/
theorem exists_prismCompletedTensor_right_equiv {C' : Type u} [CommRing C'] [Algebra A C']
    (F' : DeltaStructure p C') (hF' : D.IsDeltaHom F' (algebraMap A C'))
    (e : C ≃+* C') (he : F.IsDeltaHom F' e.toRingHom)
    (heA : e.toRingHom.comp (algebraMap A C) = algebraMap A C') :
    let H' := PrismCompletedTensor (A := A) (C := C') Q
    ∃ k : H ≃+* H',
      (prismCompletedTensorDelta Q D F hQ hF).IsDeltaHom
        (prismCompletedTensorDelta Q D F' hQ hF') k.toRingHom ∧
      k.toRingHom.comp (prismCompletedTensorLeft Q) = prismCompletedTensorLeft Q ∧
      k.toRingHom.comp (prismCompletedTensorRight Q) =
        (prismCompletedTensorRight Q).comp e.toRingHom := by
  let H' := PrismCompletedTensor (A := A) (C := C') Q
  let G := prismCompletedTensorDelta Q D F hQ hF
  let G' := prismCompletedTensorDelta Q D F' hQ hF'
  let l₀ : B →+* H := prismCompletedTensorLeft Q
  let r₀ : C →+* H := prismCompletedTensorRight Q
  let l₁ : B →+* H' := prismCompletedTensorLeft Q
  let r₁ : C' →+* H' := prismCompletedTensorRight Q
  have hw₁ : l₁.comp (algebraMap A B) = (r₁.comp e.toRingHom).comp (algebraMap A C) := by
    ext a
    change l₁ (algebraMap A B a) = r₁ (e (algebraMap A C a))
    rw [show e (algebraMap A C a) = algebraMap A C' a from RingHom.congr_fun heA a]
    exact RingHom.congr_fun (prismCompletedTensor_square Q) a
  have heA' : e.symm.toRingHom.comp (algebraMap A C') = algebraMap A C := by
    rw [← heA]
    ext a
    exact e.symm_apply_apply _
  have hw₀ : l₀.comp (algebraMap A B) =
      (r₀.comp e.symm.toRingHom).comp (algebraMap A C') := by
    ext a
    change l₀ (algebraMap A B a) = r₀ (e.symm (algebraMap A C' a))
    rw [show e.symm (algebraMap A C' a) = algebraMap A C a from RingHom.congr_fun heA' a]
    exact RingHom.congr_fun (prismCompletedTensor_square Q) a
  obtain ⟨k, hk, _⟩ := existsUnique_prismCompletedTensorHom Q D F hQ hF G' l₁ _
    (prismCompletedTensorLeft_isDeltaHom Q D F' hQ hF')
    ((prismCompletedTensorRight_isDeltaHom Q D F' hQ hF').comp he) hw₁
    (prismCompletedTensor_complete_p Q) (prismCompletedTensor_complete_generator Q)
  obtain ⟨j', hj', _⟩ := existsUnique_prismCompletedTensorHom Q D F' hQ hF' G l₀ _
    (prismCompletedTensorLeft_isDeltaHom Q D F hQ hF)
    ((prismCompletedTensorRight_isDeltaHom Q D F hQ hF).comp he.symm) hw₀
    (prismCompletedTensor_complete_p Q) (prismCompletedTensor_complete_generator Q)
  have h₀ : j'.comp k = RingHom.id H := by
    apply prismCompletedTensorHom_ext Q D F hQ hF G (hj'.1.comp hk.1) G.isDeltaHom_id
    · change (j'.comp k).comp l₀ = (RingHom.id H).comp l₀
      rw [RingHom.comp_assoc, hk.2.1, hj'.2.1, RingHom.id_comp]
    · change (j'.comp k).comp r₀ = (RingHom.id H).comp r₀
      rw [RingHom.comp_assoc, hk.2.2, ← RingHom.comp_assoc, hj'.2.2, RingHom.id_comp]
      ext x
      change r₀ (e.symm (e x)) = r₀ x
      rw [RingEquiv.symm_apply_apply]
    · exact prismCompletedTensor_complete_p Q
    · exact prismCompletedTensor_complete_generator Q
  have h₁ : k.comp j' = RingHom.id H' := by
    apply prismCompletedTensorHom_ext Q D F' hQ hF' G' (hk.1.comp hj'.1) G'.isDeltaHom_id
    · change (k.comp j').comp l₁ = (RingHom.id H').comp l₁
      rw [RingHom.comp_assoc, hj'.2.1, hk.2.1, RingHom.id_comp]
    · change (k.comp j').comp r₁ = (RingHom.id H').comp r₁
      rw [RingHom.comp_assoc, hj'.2.2, ← RingHom.comp_assoc, hk.2.2, RingHom.id_comp]
      ext x
      change r₁ (e (e.symm x)) = r₁ x
      rw [RingEquiv.apply_symm_apply]
    · exact prismCompletedTensor_complete_p Q
    · exact prismCompletedTensor_complete_generator Q
  exact ⟨RingEquiv.ofRingHom k j' h₁ h₀, hk⟩

end CompletedTensor

end SerrePositivity.BhattScholze
