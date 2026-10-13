module

public import SerrePositivity.LengthAlgebra.RootTowerLength.AdditivityFinite
public import SerrePositivity.LengthAlgebra.RootTowerLength.AdditivityApproximation
public import Mathlib.RingTheory.Finiteness.Ideal
public import SerrePositivity.CommutativeAlgebra.FinitePresentationTorsionCover

/-! # 生の正規化長さの加法性

有限段の比較と商の下限公式から、有限表示な冪ねじれ加群の任意の部分加群について
加法性を導く。有限表示な被覆で有限生成加群へ広げ、有限生成部分による近似を通じて
一様冪ねじれ加群の任意の短完全列へ適用する。
組み立てた長さ構造や加法性の引用は使わない。
-/

@[expose] public noncomputable section

set_option linter.style.haveILetI false

universe u
open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
  (ht : ∀ i, t i ∈ maximalIdeal A)

include ht

/-- 有限表示な冪ねじれの塔加群の有限生成部分加群は、
共通の有限段で実現できるため、それ自身も有限表示である。 -/
theorem finitePresentation_submodule_of_fg_of_powTorsion (M : Type u)
    [AddCommGroup M] [Module (Tower A t p) M]
    [Module.FinitePresentation (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M)
    (N : Submodule (Tower A t p) M) (hN : N.FG) :
    Module.FinitePresentation (Tower A t p) N := by
  obtain ⟨n, V, i₁, i₂, hV, _, ⟨e⟩⟩ := exists_descent A t p M hM
  let N' := N.map e.toLinearMap
  obtain ⟨k, hnk, K, hQ, ⟨eK⟩, _⟩ :=
    exists_stage_submodule_and_quotient_equiv A t p ht n V hV N' (hN.map e.toLinearMap)
  letI := (towerMap A t p n k hnk).toRingHom.toAlgebra
  letI := isScalarTower_towerMap_tower A t p n k hnk
  have hK : IsFiniteLength (TowerStage A t p k) K :=
    IsFiniteLength.of_injective hQ (Submodule.subtype_injective K)
  haveI : IsNoetherian (TowerStage A t p k) K :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hK).1
  haveI : Module.FinitePresentation (TowerStage A t p k) K :=
    Module.finitePresentation_of_finite (TowerStage A t p k) K
  haveI : Module.FinitePresentation (Tower A t p)
      (Tower A t p ⊗[TowerStage A t p k] K) := by
    obtain ⟨a, U, eU, hU⟩ := Module.FinitePresentation.exists_fin (TowerStage A t p k) K
    obtain ⟨b, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hU
    let D := Submodule.span (Tower A t p) (Set.range (stageToTower A t p k ∘ r))
    let eT : (Tower A t p ⊗[TowerStage A t p k] K) ≃ₗ[Tower A t p]
        ((Fin a → Tower A t p) ⧸ D) :=
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Tower A t p) (Tower A t p))
        (eU.trans (Submodule.quotEquivOfEq _ _ hr.symm))).trans
          (baseChangeQuotEquiv (Tower A t p) r)
    haveI : Module.FinitePresentation (Tower A t p) ((Fin a → Tower A t p) ⧸ D) := by
      apply Module.finitePresentation_of_surjective D.mkQ D.mkQ_surjective
      rw [Submodule.ker_mkQ]
      exact Submodule.fg_span (Set.finite_range _)
    exact Module.FinitePresentation.of_equiv eT.symm
  let eN : N ≃ₗ[Tower A t p] N' :=
    Submodule.equivMapOfInjective e.toLinearMap e.injective N
  exact Module.FinitePresentation.of_equiv (eK.trans eN.symm)

/-- 有限生成加群が有限表示な冪ねじれ加群へ単射で入れば、それ自身も有限表示。 -/
theorem finitePresentation_of_finite_of_injective_into_powTorsion
    (P : Type u) [AddCommGroup P] [Module (Tower A t p) P]
    [Module.FinitePresentation (Tower A t p) P]
    (hP : IsPowTorsion (towerMaxIdeal A t p) P)
    (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] [Module.Finite (Tower A t p) M]
    (f : M →ₗ[Tower A t p] P) (hf : Function.Injective f) :
    Module.FinitePresentation (Tower A t p) M := by
  have hrange : (LinearMap.range f).FG := by
    simpa only [Submodule.map_top] using (Module.Finite.fg_top (R := Tower A t p) (M := M)).map f
  haveI := finitePresentation_submodule_of_fg_of_powTorsion A t p ht P hP
    (LinearMap.range f) hrange
  exact Module.FinitePresentation.of_equiv (LinearEquiv.ofInjective f hf).symm

/-- 有限表示な冪ねじれ加群の生の正規化長さは有限である。 -/
theorem towerLengthFun_ne_top_of_finitePresentation (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Module.FinitePresentation (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M) : towerLengthFun A t p M ≠ ⊤ := by
  obtain ⟨n, V, i₁, i₂, hV, _, ⟨e⟩⟩ := exists_descent A t p M hM
  rw [towerLengthFun_congr e, towerLengthFun_tensor_eq_length A t p ht n V hV]
  apply ENNReal.div_ne_top
  · exact_mod_cast Module.length_ne_top_iff.mpr hV
  · exact_mod_cast pow_ne_zero (n * h) (Fact.out : p.Prime).ne_zero

/-- 部分加群の長さは、全体の中の有限生成部分加群で、
その部分加群に含まれるものの長さの上限に等しい。 -/
theorem towerLengthFun_submodule_eq_iSup_fg_le
    {M : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    (K : Submodule (Tower A t p) M) :
    towerLengthFun A t p K =
      ⨆ L : {L : Submodule (Tower A t p) M // L.FG ∧ L ≤ K}, towerLengthFun A t p L.val := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun S hS ↦ ?_
    let L := S.map K.subtype
    have hLK : L ≤ K := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    haveI : Module.Finite (Tower A t p) S := Module.Finite.iff_fg.mpr hS
    rw [← towerLengthFun_eq_fgLength_of_noetherian A t p ht S]
    have he := towerLengthFun_congr (A := A) (t := t) (p := p)
      (Submodule.equivMapOfInjective K.subtype K.subtype_injective S)
    exact he ▸ le_iSup (fun L : {L : Submodule (Tower A t p) M // L.FG ∧ L ≤ K} ↦
      towerLengthFun A t p L.val) ⟨L, hS.map K.subtype, hLK⟩
  · refine iSup_le fun L ↦ ?_
    exact towerLengthFun_le_of_injective A t p
      (Submodule.inclusion L.property.2) (Submodule.inclusion_injective _)

/-- 有限生成加群の商の生の長さは、分母の有限生成部分による商の長さの下限に等しい。 -/
theorem towerLengthFun_quotient_eq_iInf_fg_le (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Module.Finite (Tower A t p) M]
    (K : Submodule (Tower A t p) M) :
    towerLengthFun A t p (M ⧸ K) =
      ⨅ L : {L : Submodule (Tower A t p) M // L.FG ∧ L ≤ K},
        towerLengthFun A t p (M ⧸ L.val) := by
  have hq := fgLength_quotient_eq_iInf_fg A t p M K
  simp_rw [← towerLengthFun_eq_fgLength_of_noetherian A t p ht] at hq
  rw [hq]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun L ↦ ?_
    exact iInf_le_of_le L.val (iInf_le_of_le L.property.1 (iInf_le_of_le L.property.2 le_rfl))
  · refine le_iInf fun L ↦ le_iInf fun hL ↦ le_iInf fun hLK ↦ ?_
    exact iInf_le (fun L : {L : Submodule (Tower A t p) M // L.FG ∧ L ≤ K} ↦
      towerLengthFun A t p (M ⧸ L.val)) ⟨L, hL, hLK⟩

/-- 有限表示な冪ねじれ加群の任意の部分加群について、
商の下限公式と部分加群の上限公式から加法性を導く。 -/
theorem towerLengthFun_add_submodule_finitePresentation (M : Type u)
    [AddCommGroup M] [Module (Tower A t p) M]
    [Module.FinitePresentation (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M)
    (K : Submodule (Tower A t p) M) :
    towerLengthFun A t p M = towerLengthFun A t p K + towerLengthFun A t p (M ⧸ K) := by
  let ι := {L : Submodule (Tower A t p) M // L.FG ∧ L ≤ K}
  letI : Nonempty ι := ⟨⟨⊥, Submodule.fg_bot, bot_le⟩⟩
  have hadd (L : ι) : towerLengthFun A t p M =
      towerLengthFun A t p L.val + towerLengthFun A t p (M ⧸ L.val) :=
    towerLengthFun_add_submodule_of_finitePresentation A t p ht M hM L.val L.property.1
  refine le_antisymm ?_ ?_
  · rw [towerLengthFun_quotient_eq_iInf_fg_le A t p ht M K, ENNReal.add_iInf]
    refine le_iInf fun L ↦ ?_
    rw [hadd L]
    exact add_le_add (towerLengthFun_le_of_injective A t p
      (Submodule.inclusion L.property.2) (Submodule.inclusion_injective _)) le_rfl
  · rw [towerLengthFun_submodule_eq_iSup_fg_le A t p ht K, ENNReal.iSup_add]
    refine iSup_le fun L ↦ ?_
    calc
      towerLengthFun A t p L.val + towerLengthFun A t p (M ⧸ K) ≤
          towerLengthFun A t p L.val + towerLengthFun A t p (M ⧸ L.val) :=
        add_le_add le_rfl (towerLengthFun_le_of_surjective A t p
          (Submodule.factor L.property.2) (Submodule.factor_surjective _))
      _ = towerLengthFun A t p M := (hadd L).symm

/-- 有限表示な冪ねじれ加群の部分加群から有限生成加群への全射では、
核の長さと像の長さの和が元の長さに等しい。有限生成部分を上限で比較する。 -/
theorem towerLengthFun_add_kernel_of_submodule_finitePresentation
    (P : Type u) [AddCommGroup P] [Module (Tower A t p) P]
    [Module.FinitePresentation (Tower A t p) P]
    (hP : IsPowTorsion (towerMaxIdeal A t p) P)
    (L : Submodule (Tower A t p) P)
    (N : Type u) [AddCommGroup N] [Module (Tower A t p) N] [Module.Finite (Tower A t p) N]
    (f : L →ₗ[Tower A t p] N) (hf : Function.Surjective f) :
    towerLengthFun A t p L = towerLengthFun A t p f.ker + towerLengthFun A t p N := by
  have hL : IsPowTorsion (towerMaxIdeal A t p) L := hP.submodule L
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun S hS ↦ ?_
    haveI : Module.Finite (Tower A t p) S := Module.Finite.iff_fg.mpr hS
    haveI : Module.FinitePresentation (Tower A t p) S :=
      finitePresentation_of_finite_of_injective_into_powTorsion A t p ht P hP S
        (L.subtype.comp S.subtype) (L.subtype_injective.comp S.subtype_injective)
    let F := f.comp S.subtype
    let ιK : F.ker →ₗ[Tower A t p] f.ker :=
      { toFun := fun x ↦ ⟨(x.val : L), x.property⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hιK : Function.Injective ιK := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun v : f.ker ↦ v.val) hxy
    have hSadd := towerLengthFun_add_submodule_finitePresentation A t p ht S
      (hL.submodule S) F.ker
    rw [towerLengthFun_congr F.quotKerEquivRange] at hSadd
    rw [← towerLengthFun_eq_fgLength_of_noetherian A t p ht S, hSadd]
    exact add_le_add (towerLengthFun_le_of_injective A t p ιK hιK)
      (towerLengthFun_submodule_le A t p F.range)
  · obtain ⟨W, hW, hWmap⟩ := exists_fg_submodule_map_eq_of_surjective A t p f hf
      (⊤ : Submodule (Tower A t p) N) Module.Finite.fg_top
    let ι := {U : Submodule (Tower A t p) L // U.FG ∧ U ≤ f.ker}
    letI : Nonempty ι := ⟨⟨⊥, Submodule.fg_bot, bot_le⟩⟩
    rw [towerLengthFun_submodule_eq_iSup_fg_le A t p ht f.ker, ENNReal.iSup_add]
    refine iSup_le fun U ↦ ?_
    let S : Submodule (Tower A t p) L := U.val ⊔ W
    have hS : S.FG := U.property.1.sup hW
    haveI : Module.Finite (Tower A t p) S := Module.Finite.iff_fg.mpr hS
    haveI : Module.FinitePresentation (Tower A t p) S :=
      finitePresentation_of_finite_of_injective_into_powTorsion A t p ht P hP S
        (L.subtype.comp S.subtype) (L.subtype_injective.comp S.subtype_injective)
    let F := f.comp S.subtype
    have hF : Function.Surjective F := by
      intro n
      have hn : n ∈ W.map f := hWmap.symm ▸ Submodule.mem_top
      obtain ⟨x, hx, hxn⟩ := Submodule.mem_map.mp hn
      exact ⟨⟨x, (show W ≤ S from le_sup_right) hx⟩, hxn⟩
    let ιU : U.val →ₗ[Tower A t p] F.ker :=
      { toFun := fun x ↦ ⟨⟨x.val, (show U.val ≤ S from le_sup_left) x.property⟩,
          U.property.2 x.property⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hιU : Function.Injective ιU := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun v : F.ker ↦ (v.val : L)) hxy)
    have hSadd := towerLengthFun_add_submodule_finitePresentation A t p ht S
      (hL.submodule S) F.ker
    rw [towerLengthFun_congr (F.quotKerEquivOfSurjective hF)] at hSadd
    calc
      towerLengthFun A t p U.val + towerLengthFun A t p N ≤
          towerLengthFun A t p F.ker + towerLengthFun A t p N :=
        add_le_add (towerLengthFun_le_of_injective A t p ιU hιU) le_rfl
      _ = towerLengthFun A t p S := hSadd.symm
      _ ≤ towerLengthFun A t p L := towerLengthFun_submodule_le A t p S

/-- 有限生成な冪ねじれ加群と有限生成部分加群の商の間で、生の長さは加法的。
有限表示な冪ねじれ被覆で二つの部分加群を比較し、有限な核の長さを相殺する。 -/
theorem towerLengthFun_add_submodule_of_finite (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Module.Finite (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M)
    (N : Submodule (Tower A t p) M) (hN : N.FG) :
    towerLengthFun A t p M = towerLengthFun A t p N + towerLengthFun A t p (M ⧸ N) := by
  have hJ : (towerMaxIdeal A t p).FG :=
    Ideal.FG.map (IsNoetherian.noetherian (maximalIdeal A)) (algebraMap A (Tower A t p))
  obtain ⟨P, hfp, hP, g, hg⟩ := exists_finitePresentation_powTorsion_cover
    (towerMaxIdeal A t p) hJ M hM
  haveI := hfp
  haveI : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
  let K := g.ker
  let L := N.comap g
  let f : L →ₗ[Tower A t p] N :=
    { toFun := fun x ↦ ⟨g x, x.property⟩
      map_add' := fun x y ↦ Subtype.ext (g.map_add x y)
      map_smul' := fun a x ↦ Subtype.ext (g.map_smul a x) }
  have hf : Function.Surjective f := by
    intro n
    obtain ⟨x, hx⟩ := hg n.val
    exact ⟨⟨x, by change g x ∈ N; rw [hx]; exact n.property⟩, Subtype.ext hx⟩
  let ιK : f.ker →ₗ[Tower A t p] K :=
    { toFun := fun x ↦ ⟨(x.val : P), congrArg (fun y : N ↦ y.val) x.property⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hιKi : Function.Injective ιK := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K ↦ z.val) hxy
  have hιKs : Function.Surjective ιK := by
    intro x
    have hxL : x.val ∈ L := by
      change g x.val ∈ N
      rw [x.property]
      exact N.zero_mem
    have hxK : (⟨x.val, hxL⟩ : L) ∈ f.ker := by
      apply Subtype.ext
      exact x.property
    exact ⟨⟨⟨x.val, hxL⟩, hxK⟩, rfl⟩
  let eK := LinearEquiv.ofBijective ιK ⟨hιKi, hιKs⟩
  have hLK := towerLengthFun_add_kernel_of_submodule_finitePresentation A t p ht P hP
    L N f hf
  rw [towerLengthFun_congr eK] at hLK
  have hPK := towerLengthFun_add_submodule_finitePresentation A t p ht P hP K
  rw [towerLengthFun_congr (g.quotKerEquivOfSurjective hg)] at hPK
  let π := N.mkQ.comp g
  have hπ : Function.Surjective π := N.mkQ_surjective.comp hg
  have hπker : π.ker = L := by
    ext x
    change N.mkQ (g x) = 0 ↔ g x ∈ N
    exact Submodule.Quotient.mk_eq_zero N
  let eQ := (Submodule.quotEquivOfEq _ _ hπker.symm).trans (π.quotKerEquivOfSurjective hπ)
  have hPL := towerLengthFun_add_submodule_finitePresentation A t p ht P hP L
  rw [towerLengthFun_congr eQ] at hPL
  have hKfin : towerLengthFun A t p K ≠ ⊤ :=
    ne_top_of_le_ne_top (towerLengthFun_ne_top_of_finitePresentation A t p ht P hP)
      (towerLengthFun_submodule_le A t p K)
  apply (ENNReal.add_right_inj hKfin).mp
  calc
    towerLengthFun A t p K + towerLengthFun A t p M = towerLengthFun A t p P := hPK.symm
    _ = towerLengthFun A t p L + towerLengthFun A t p (M ⧸ N) := hPL
    _ = towerLengthFun A t p K +
        (towerLengthFun A t p N + towerLengthFun A t p (M ⧸ N)) := by rw [hLK, add_assoc]

/-- Noether 局所基底・素数・座標の極大イデアル所属の下で、
一様冪ねじれ加群の任意の短完全列について生の長さは加法的。 -/
theorem towerLengthFun_add_of_exact_of_noetherian
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module (Tower A t p) M₁]
    [AddCommGroup M₂] [Module (Tower A t p) M₂]
    [AddCommGroup M₃] [Module (Tower A t p) M₃]
    (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂) :
    towerLengthFun A t p M₂ = towerLengthFun A t p M₁ + towerLengthFun A t p M₃ := by
  exact towerLengthFun_add_of_exact_of_fg_additivity A t p ht
    (fun M _ _ _ K hK hM ↦ towerLengthFun_add_submodule_of_finite A t p ht M hM K hK)
    f g hf hg hfg hM₂

end SerrePositivity.Section2
