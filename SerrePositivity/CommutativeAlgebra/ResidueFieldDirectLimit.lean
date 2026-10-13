module

public import SerrePositivity.CommutativeAlgebra.DirectLimitLocalRing
public import SerrePositivity.CommutativeAlgebra.DirectLimitFlat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs

/-! # 剰余体拡大の有向図式の極限段

実際の両立する有向図式に対して、基底の極大イデアルの拡張を保持する。
指定体への両立する写像が体全体を覆えば、直極限の剰余体をその体へ同定する。
図式の存在やNoether性は仮定・結論へ隠さず、別の構成課題とする。
-/

public section
namespace SerrePositivity
open IsLocalRing
variable {B ι : Type*} [CommRing B] [IsLocalRing B]
variable [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
variable [∀ i, Algebra B (S i)]
variable (f : ∀ i j, i ≤ j → S i →ₐ[B] S j) [DirectedSystem S (f · · ·)]

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
/-- 基底から直極限への係数写像は、どの段を経由しても同じ写像である。 -/
theorem directLimit_algebraMap_comp (i : ι) :
    (DirectLimit.Ring.of S f i).comp (algebraMap B (S i)) =
      algebraMap B (DirectLimit S f) := by
  ext b
  exact (DirectLimit.Algebra.of S f i).commutes b

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
/-- 局所な遷移写像と局所な係数写像の直極限では、基底の係数写像も局所。 -/
theorem directLimit_algebraMap_isLocalHom
    [∀ i, IsLocalHom (algebraMap B (S i))]
    (hlocal : ∀ i j h, IsLocalHom (f i j h).toRingHom) :
    IsLocalHom (algebraMap B (DirectLimit S f)) := by
  let i := Classical.arbitrary ι
  let : IsLocalHom (DirectLimit.Ring.of S f i) := directLimit_isLocalHom S f hlocal i
  rw [← directLimit_algebraMap_comp S f i]
  infer_instance

/-- 各段で基底の極大イデアルを拡張していれば、直極限でも同じ等式が成立する。
極大イデアルの有限生成性・Noether性は不要。 -/
theorem directLimit_maximalIdeal_map
    [∀ i, IsLocalHom (algebraMap B (S i))]
    (hlocal : ∀ i j h, IsLocalHom (f i j h).toRingHom)
    (hmax : ∀ i, (maximalIdeal B).map (algebraMap B (S i)) = maximalIdeal (S i))
    [IsLocalRing (DirectLimit S f)] :
    (maximalIdeal B).map (algebraMap B (DirectLimit S f)) = maximalIdeal (DirectLimit S f) := by
  let : IsLocalHom (algebraMap B (DirectLimit S f)) :=
    directLimit_algebraMap_isLocalHom S f hlocal
  refine le_antisymm (IsLocalRing.map_maximalIdeal_le _) ?_
  intro x hx
  obtain ⟨i, a, ha⟩ := DirectLimit.exists_eq_mk f x
  have ha' : DirectLimit.Ring.of S f i a = x := by with_unfolding_all exact ha.symm
  have ham : a ∈ maximalIdeal (S i) := fun hu ↦ hx (ha' ▸ hu.map (DirectLimit.Ring.of S f i))
  rw [← hmax i] at ham
  have hm := Ideal.mem_map_of_mem (DirectLimit.Ring.of S f i) ham
  rw [Ideal.map_map, directLimit_algebraMap_comp S f i, ha'] at hm
  exact hm

/-- Noether基底から極大イデアルを拡張した極限の極大イデアルは有限生成。
極限環自身のNoether性は結論しない。 -/
theorem directLimit_maximalIdeal_fg [IsNoetherianRing B]
    [∀ i, IsLocalHom (algebraMap B (S i))]
    (hlocal : ∀ i j h, IsLocalHom (f i j h).toRingHom)
    (hmax : ∀ i, (maximalIdeal B).map (algebraMap B (S i)) = maximalIdeal (S i))
    [IsLocalRing (DirectLimit S f)] : (maximalIdeal (DirectLimit S f)).FG := by
  classical
  rw [← directLimit_maximalIdeal_map S f hlocal hmax]
  obtain ⟨t, ht⟩ := (maximalIdeal B).fg_of_isNoetherianRing
  refine ⟨t.image (algebraMap B (DirectLimit S f)), ?_⟩
  rw [Finset.coe_image, ← Ideal.map_span, ht]

section Residue
variable {K : Type*} [Field K] [Algebra B K]
variable (g : ∀ i, S i →ₐ[B] K)
variable (hg : ∀ i j h x, g j (f i j h x) = g i x)
variable (hcover : ∀ x : K, ∃ i, ∃ y : S i, g i y = x)

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
include hcover in
/-- 体全体を覆う両立する段写像は、直極限からの全射を与える。 -/
theorem directLimit_fieldLift_surjective :
    Function.Surjective (DirectLimit.Algebra.lift S f K g hg) := by
  intro x
  obtain ⟨i, y, hy⟩ := hcover x
  exact ⟨DirectLimit.Algebra.of S f i y, hy⟩

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
/-- 指定体を覆う図式の直極限の剰余体同型。
局所性は別に供給し、適用の入口では局所環の保存定理を使う。 -/
noncomputable def directLimitResidueEquiv [IsLocalRing (DirectLimit S f)] :
    ResidueField (DirectLimit S f) ≃+* K := by
  let G := (DirectLimit.Algebra.lift S f K g hg).toRingHom
  have hsurj : Function.Surjective G := directLimit_fieldLift_surjective S f g hg hcover
  have hker : RingHom.ker G = maximalIdeal (DirectLimit S f) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective G hsurj)
  exact (Ideal.quotEquivOfEq hker.symm).trans (G.quotientKerEquivOfSurjective hsurj)

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
/-- 剰余体同型は、各段の元に対して元の指定体への写像と一致する。 -/
@[simp] theorem directLimitResidueEquiv_of [IsLocalRing (DirectLimit S f)] (i : ι) (x : S i) :
    directLimitResidueEquiv S f g hg hcover
      (residue (DirectLimit S f) (DirectLimit.Ring.of S f i x)) = g i x := by
  simp only [directLimitResidueEquiv, residue]
  rfl

omit [∀ i, IsLocalRing (S i)] in
/-- 指定体の剰余体代数構造と両立する図式なら、極限の同型も元の剰余体上で両立する。 -/
theorem directLimitResidueEquiv_map
    [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
    [IsLocalRing (DirectLimit S f)] [IsLocalHom (algebraMap B (DirectLimit S f))]
    (x : ResidueField B) :
    directLimitResidueEquiv S f g hg hcover
      (ResidueField.map (algebraMap B (DirectLimit S f)) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
  rw [ResidueField.map_residue]
  let i := Classical.arbitrary ι
  rw [← directLimit_algebraMap_comp S f i, RingHom.comp_apply,
    directLimitResidueEquiv_of, (g i).commutes]
  exact IsScalarTower.algebraMap_apply B (ResidueField B) K b


end Residue

universe u
/-- 実際の有向図式から、指定体を剰余体に持つ平坦局所拡大を構成する。
添字と段の型がType uなら極限もType u。図式の存在・完備性・Noether性は別課題。 -/
theorem exists_flat_local_extension_of_directed_system
    {B ι K : Type u} [CommRing B] [IsLocalRing B]
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    [Field K] [Algebra (ResidueField B) K] [Algebra B K]
    [IsScalarTower B (ResidueField B) K]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra B (S i)] [∀ i, IsLocalHom (algebraMap B (S i))]
    [∀ i, Module.Flat B (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[B] S j) [DirectedSystem S (f · · ·)]
    (hlocal : ∀ i j h, IsLocalHom (f i j h).toRingHom)
    (hmax : ∀ i, (maximalIdeal B).map (algebraMap B (S i)) = maximalIdeal (S i))
    (g : ∀ i, S i →ₐ[B] K) (hg : ∀ i j h x, g j (f i j h x) = g i x)
    (hcover : ∀ x : K, ∃ i, ∃ y : S i, g i y = x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  let C := DirectLimit S f
  let : IsLocalRing C := directLimit_isLocalRing S f
  let : IsLocalHom (algebraMap B C) := directLimit_algebraMap_isLocalHom S f hlocal
  let : Module.Flat B C := directLimit_flat S f
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    directLimit_maximalIdeal_map S f hlocal hmax, directLimitResidueEquiv S f g hg hcover,
    directLimitResidueEquiv_map S f g hg hcover⟩

end SerrePositivity
