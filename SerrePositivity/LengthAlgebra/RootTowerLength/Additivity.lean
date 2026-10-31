module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Finiteness.Ideal
public import SerrePositivity.CommutativeAlgebra.FinitePresentationTorsionCover
public import SerrePositivity.LengthAlgebra.Normalized

/-! # 根の塔の正規化長さの加法性と構成

## 概要

有限生成部分加群による一般の λ∞ の近似と単調性、有限段の短完全列から導く数値関数の加法性、有限表示な冪ねじれ加群の任意の部分加群への加法性の拡張を示し、Noether 局所基底と極大イデアル内の座標について具体的な `NormalizedLength` を構成する。

## 方針

有限生成部分加群とその商を共通の有限段で実現し、有限表示な被覆で有限生成加群へ広げる。

## 規約

長さの法則を引用で補わない。C2 の引用や旧 Paper 層の構成には依存しない。

## 使われ方

`RootTowerLength/Completion`、CLMST の長さ、Paper の長さ代数。
-/

@[expose] public noncomputable section

universe u v

section AdditivityApproximationPart

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity.Section2

set_option backward.isDefEq.respectTransparency false

/-- 有限表示な被覆を有限生成加群の商へ写す全射は、分母の有限生成部分に既に降りる。
関係式の像と、有限個の生成元を被覆の像へ補正する差だけを分母に加える。 -/
theorem exists_fg_quotient_cover_of_finitePresentation
    {R : Type u} [CommRing R] {M P : Type u}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (K : Submodule R M) (f : P →ₗ[R] M ⧸ K) (hf : Function.Surjective f) :
    ∃ L : Submodule R M, L.FG ∧ L ≤ K ∧
      ∃ g : P →ₗ[R] M ⧸ L, Function.Surjective g := by
  classical
  obtain ⟨l, U, e, hU⟩ := Module.FinitePresentation.exists_fin R P
  let π : (Fin l → R) →ₗ[R] P := e.symm.toLinearMap.comp U.mkQ
  have hπ : Function.Surjective π := e.symm.surjective.comp U.mkQ_surjective
  obtain ⟨g, hg⟩ := Module.projective_lifting_property K.mkQ (f.comp π) K.mkQ_surjective
  have hge (x : Fin l → R) : K.mkQ (g x) = f (π x) := DFunLike.congr_fun hg x
  obtain ⟨r, z, hz⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose w hw using fun i => (hf.comp hπ) (K.mkQ (z i))
  have hw' (i : Fin r) : f (π (w i)) = K.mkQ (z i) := hw i
  let y := fun i => z i - g (w i)
  let L : Submodule R M := U.map g ⊔ Submodule.span R (Set.range y)
  have hUK : U.map g ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change K.mkQ (g x) = 0
    rw [hge]
    have hπx : π x = 0 := by
      change e.symm (U.mkQ x) = 0
      have hUx : U.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
      rw [hUx, map_zero]
    rw [hπx, map_zero]
  have hyK : Submodule.span R (Set.range y) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change K.mkQ (z i - g (w i)) = 0
    rw [map_sub, hge, hw', sub_self]
  have hLK : L ≤ K := sup_le hUK hyK
  have hkill : U ≤ (L.mkQ.comp g).ker := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((show U.map g ≤ L from le_sup_left) (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))
  let F : P →ₗ[R] M ⧸ L := (U.liftQ (L.mkQ.comp g) hkill).comp e.toLinearMap
  have hFπ (x : Fin l → R) : F (π x) = L.mkQ (g x) := by
    simp only [F, π, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, Submodule.liftQ_apply, Submodule.mkQ_apply]
  have hspan : Submodule.span R (Set.range fun i => L.mkQ (z i)) = ⊤ := by
    change Submodule.span R (Set.range (L.mkQ ∘ z)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, hz, Submodule.map_top,
      LinearMap.range_eq_top.mpr L.mkQ_surjective]
  have hF : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨π (w i), ?_⟩
    rw [hFπ]
    symm
    rw [← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((show Submodule.span R (Set.range y) ≤ L from le_sup_right)
        (Submodule.subset_span (Set.mem_range_self i)))
  exact ⟨L, (hU.map g).sup (Submodule.fg_span (Set.finite_range y)), hLK, F, hF⟩

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 塔上の生の `λ∞` は単射で単調。部分加群の像と線形同型不変性だけで従う。 -/
theorem towerLengthFun_le_of_injective
    {M N : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup N] [Module (Tower A t p) N]
    (f : M →ₗ[Tower A t p] N) (hf : Function.Injective f) :
    towerLengthFun A t p M ≤ towerLengthFun A t p N := by
  apply iSup₂_le
  intro S hS
  apply le_iSup₂_of_le (S.map f) (hS.map f)
  exact le_of_eq (fgLength_congr (Submodule.equivMapOfInjective f hf S))

/-- 生の `λ∞` の部分加群の値は全体の値以下。 -/
theorem towerLengthFun_submodule_le
    {M : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    (S : Submodule (Tower A t p) M) : towerLengthFun A t p S ≤ towerLengthFun A t p M :=
  towerLengthFun_le_of_injective A t p S.subtype S.subtype_injective

/-- 全射の先の有限生成部分加群は、元の有限生成部分加群の像として得られる。 -/
theorem exists_fg_submodule_map_eq_of_surjective
    {M N : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup N] [Module (Tower A t p) N]
    (f : M →ₗ[Tower A t p] N) (hf : Function.Surjective f)
    (S : Submodule (Tower A t p) N) (hS : S.FG) :
    ∃ T : Submodule (Tower A t p) M, T.FG ∧ T.map f = S := by
  classical
  obtain ⟨r, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hS
  choose y hy using fun j => hf (z j)
  refine ⟨Submodule.span (Tower A t p) (Set.range y), Submodule.fg_span (Set.finite_range y), ?_⟩
  rw [Submodule.map_span, ← Set.range_comp]
  simpa only [Function.comp_def, hy] using hz

/-- 生の `λ∞` は全射で単調。有限生成部分加群の生成元だけを持ち上げればよい。 -/
theorem towerLengthFun_le_of_surjective
    {M N : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup N] [Module (Tower A t p) N]
    (f : M →ₗ[Tower A t p] N) (hf : Function.Surjective f) :
    towerLengthFun A t p N ≤ towerLengthFun A t p M := by
  apply iSup₂_le
  intro S hS
  obtain ⟨T, hT, hTS⟩ := exists_fg_submodule_map_eq_of_surjective A t p f hf S hS
  let fT : T →ₗ[Tower A t p] S :=
    { toFun := fun x => ⟨f x, hTS ▸ Submodule.mem_map.mpr ⟨x, x.2, rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (f.map_add _ _)
      map_smul' := fun _ _ => Subtype.ext (f.map_smul _ _) }
  have hsur : Function.Surjective fT := by
    intro x
    have hx : (x : N) ∈ T.map f := hTS.symm ▸ x.2
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.mp hx
    exact ⟨⟨y, hy⟩, Subtype.ext hfy⟩
  exact (fgLength_le_of_surjective fT hsur).trans (le_iSup₂_of_le T hT le_rfl)

/-- 有限生成加群の商の `λ*` は、分母の有限生成部分による商の値の下限。
有限表示な被覆が有限個の関係式だけを使うことから、定義だけで導く。 -/
theorem fgLength_quotient_eq_iInf_fg
    (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] [Module.Finite (Tower A t p) M]
    (K : Submodule (Tower A t p) M) :
    fgLength A t p (M ⧸ K) =
      ⨅ (L : Submodule (Tower A t p) M) (_ : L.FG) (_ : L ≤ K), fgLength A t p (M ⧸ L) := by
  apply le_antisymm
  · refine le_iInf fun L => le_iInf fun _ => le_iInf fun hLK => ?_
    exact fgLength_le_of_surjective (Submodule.factor hLK) (Submodule.factor_surjective hLK)
  · unfold fgLength
    refine le_iInf fun P => le_iInf fun i₁ => le_iInf fun i₂ => le_iInf fun hP =>
      le_iInf fun f => le_iInf fun hf => ?_
    obtain ⟨L, hL, hLK, g, hg⟩ := exists_fg_quotient_cover_of_finitePresentation K f hf
    refine iInf_le_of_le L (iInf_le_of_le hL (iInf_le_of_le hLK ?_))
    exact iInf_le_of_le P (iInf_le_of_le i₁ (iInf_le_of_le i₂
      (iInf_le_of_le hP (iInf_le_of_le g (iInf_le_of_le hg le_rfl)))))

variable [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)

variable (hfgadd : ∀ (M : Type u) [AddCommGroup M] [Module (Tower A t p) M]
    [Module.Finite (Tower A t p) M] (K : Submodule (Tower A t p) M), K.FG →
    IsPowTorsion (towerMaxIdeal A t p) M →
    towerLengthFun A t p M = towerLengthFun A t p K + towerLengthFun A t p (M ⧸ K))

include ht hfgadd in
/-- 有限生成の中央加群の値は、任意の部分加群の値と商の値の和以下。
有限生成分母での加法性を明示引数に取り、商の下限公式を適用する。 -/
theorem fgLength_le_towerLengthFun_submodule_add_quotient
    (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] [Module.Finite (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M) (K : Submodule (Tower A t p) M) :
    fgLength A t p M ≤ towerLengthFun A t p K + fgLength A t p (M ⧸ K) := by
  rw [fgLength_quotient_eq_iInf_fg]
  simp only [ENNReal.add_iInf]
  refine le_iInf fun L => le_iInf fun hL => le_iInf fun hLK => ?_
  let : Module.Finite (Tower A t p) L := Module.Finite.iff_fg.mpr hL
  have heq := hfgadd M L hL hM
  rw [towerLengthFun_eq_fgLength_of_noetherian A t p ht M,
    towerLengthFun_eq_fgLength_of_noetherian A t p ht L,
    towerLengthFun_eq_fgLength_of_noetherian A t p ht (M ⧸ L)] at heq
  rw [heq]
  refine add_le_add ?_ le_rfl
  rw [← towerLengthFun_eq_fgLength_of_noetherian A t p ht L]
  exact towerLengthFun_le_of_injective A t p (Submodule.inclusion hLK)
    (Submodule.inclusion_injective hLK)

include ht hfgadd in
/-- 一般の完全列の長さの上向き評価を有限生成の中央部分加群へ還元する。
核の有限生成分母による商近似が、核全体の有限生成性を不要にする。 -/
theorem towerLengthFun_le_add_of_exact_of_fg_additivity
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module (Tower A t p) M₁]
    [AddCommGroup M₂] [Module (Tower A t p) M₂]
    [AddCommGroup M₃] [Module (Tower A t p) M₃]
    (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂) :
    towerLengthFun A t p M₂ ≤ towerLengthFun A t p M₁ + towerLengthFun A t p M₃ := by
  apply iSup₂_le
  intro S hS
  let : Module.Finite (Tower A t p) S := Module.Finite.iff_fg.mpr hS
  let G : S →ₗ[Tower A t p] M₃ := g.comp S.subtype
  let K := G.ker
  let e := LinearEquiv.ofInjective f hf
  let kF : K →ₗ[Tower A t p] f.range :=
    (S.subtype.comp K.subtype).codRestrict f.range (by
      intro x
      exact (hfg x.1.1).mp x.2)
  have hkF : Function.Injective kF := by
    intro x y hxy
    have hval := congrArg (fun z : f.range => (z : M₂)) hxy
    change x.1.1 = y.1.1 at hval
    exact Subtype.ext (Subtype.ext hval)
  have hK : towerLengthFun A t p K ≤ towerLengthFun A t p M₁ :=
    towerLengthFun_le_of_injective A t p (e.symm.toLinearMap.comp kF)
      (e.symm.injective.comp hkF)
  let : Module.Finite (Tower A t p) G.range :=
    Module.Finite.of_surjective G.rangeRestrict G.surjective_rangeRestrict
  have hr : fgLength A t p G.range ≤ towerLengthFun A t p M₃ := by
    rw [← towerLengthFun_eq_fgLength_of_noetherian A t p ht G.range]
    exact towerLengthFun_submodule_le A t p G.range
  have he := fgLength_le_towerLengthFun_submodule_add_quotient A t p ht hfgadd S
    (hM₂.submodule S) K
  rw [fgLength_congr G.quotKerEquivRange] at he
  exact he.trans (add_le_add hK hr)

include ht hfgadd in
/-- 完全列の両端の有限生成部分の値の和は、中央全体の値以下。
右端の生成元を持ち上げ、左端の有限生成像と合わせて有限生成の中央部分を作る。 -/
theorem fg_endpoints_add_le_of_exact_of_fg_additivity
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module (Tower A t p) M₁]
    [AddCommGroup M₂] [Module (Tower A t p) M₂]
    [AddCommGroup M₃] [Module (Tower A t p) M₃]
    (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂)
    (L : Submodule (Tower A t p) M₁) (hL : L.FG)
    (N : Submodule (Tower A t p) M₃) (hN : N.FG) :
    fgLength A t p L + fgLength A t p N ≤ towerLengthFun A t p M₂ := by
  obtain ⟨T, hT, hTN⟩ := exists_fg_submodule_map_eq_of_surjective A t p g hg N hN
  let S : Submodule (Tower A t p) M₂ := L.map f ⊔ T
  have hS : S.FG := (hL.map f).sup hT
  let : Module.Finite (Tower A t p) S := Module.Finite.iff_fg.mpr hS
  let : Module.Finite (Tower A t p) L := Module.Finite.iff_fg.mpr hL
  have hgf : g.comp f = 0 := by
    apply LinearMap.ext
    intro x
    exact (hfg (f x)).mpr ⟨x, rfl⟩
  have hSN : S.map g = N := by
    rw [Submodule.map_sup, ← Submodule.map_comp, hgf, Submodule.map_zero, bot_sup_eq, hTN]
  let F : L →ₗ[Tower A t p] S :=
    { toFun := fun x => ⟨f x, (show L.map f ≤ S from le_sup_left)
        (Submodule.mem_map.mpr ⟨x, x.2, rfl⟩)⟩
      map_add' := fun _ _ => Subtype.ext (f.map_add _ _)
      map_smul' := fun _ _ => Subtype.ext (f.map_smul _ _) }
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    exact hf (congrArg (fun z : S => (z : M₂)) hxy)
  let G : S →ₗ[Tower A t p] N :=
    { toFun := fun x => ⟨g x, hSN ▸ Submodule.mem_map.mpr ⟨x, x.2, rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (g.map_add _ _)
      map_smul' := fun _ _ => Subtype.ext (g.map_smul _ _) }
  have hG : Function.Surjective G := by
    intro x
    have hx : (x : M₃) ∈ S.map g := hSN.symm ▸ x.2
    obtain ⟨y, hy, hgy⟩ := Submodule.mem_map.mp hx
    exact ⟨⟨y, hy⟩, Subtype.ext hgy⟩
  let K := F.range
  have hK : K.FG := by
    change F.range.FG
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map F
  let : Module.Finite (Tower A t p) K := Module.Finite.iff_fg.mpr hK
  have hKG : K ≤ G.ker := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change g (f (x : M₁)) = 0
    exact DFunLike.congr_fun hgf (x : M₁)
  let Q := K.liftQ G hKG
  have hQ : Function.Surjective Q := by
    intro x
    obtain ⟨y, hy⟩ := hG x
    exact ⟨K.mkQ y, hy⟩
  have heq := hfgadd S K hK (hM₂.submodule S)
  rw [towerLengthFun_eq_fgLength_of_noetherian A t p ht S,
    towerLengthFun_eq_fgLength_of_noetherian A t p ht K,
    towerLengthFun_eq_fgLength_of_noetherian A t p ht (S ⧸ K),
    ← fgLength_congr (LinearEquiv.ofInjective F hF)] at heq
  calc
    fgLength A t p L + fgLength A t p N ≤
        fgLength A t p L + fgLength A t p (S ⧸ K) :=
      add_le_add le_rfl (fgLength_le_of_surjective Q hQ)
    _ = fgLength A t p S := heq.symm
    _ ≤ towerLengthFun A t p M₂ := le_iSup₂_of_le S hS le_rfl

include ht hfgadd in
/-- 一般の短完全列の加法性は、有限生成の中央加群と有限生成部分加群の
正準短完全列の加法性へ還元される。有限生成・有限表示の条件を一般加群へ
密かに追加せず、商の下限と両端の上限によって両向きの評価を証明する。 -/
theorem towerLengthFun_add_of_exact_of_fg_additivity
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module (Tower A t p) M₁]
    [AddCommGroup M₂] [Module (Tower A t p) M₂]
    [AddCommGroup M₃] [Module (Tower A t p) M₃]
    (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂) :
    towerLengthFun A t p M₂ = towerLengthFun A t p M₁ + towerLengthFun A t p M₃ := by
  apply le_antisymm
    (towerLengthFun_le_add_of_exact_of_fg_additivity A t p ht hfgadd f g hf hfg hM₂)
  change (⨆ L : Submodule (Tower A t p) M₁, ⨆ (_ : L.FG), fgLength A t p L) +
    (⨆ N : Submodule (Tower A t p) M₃, ⨆ (_ : N.FG), fgLength A t p N) ≤ _
  apply ENNReal.biSup_add_biSup_le' ⟨⊥, Submodule.fg_bot⟩ ⟨⊥, Submodule.fg_bot⟩
  intro L hL N hN
  exact fg_endpoints_add_le_of_exact_of_fg_additivity A t p ht hfgadd f g hf hg hfg hM₂ L hL N hN

end SerrePositivity.Section2

end AdditivityApproximationPart

section AdditivityFinitePart

set_option linter.style.haveILetI false

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
  (ht : ∀ i, t i ∈ maximalIdeal A)

include ht

/-- 有限段から係数拡大した加群の生の上限長さは、その段の正規化した長さに等しい。
証明済みの有限生成一致を使い、旧 C1 の引用には依存しない。 -/
theorem towerLengthFun_tensor_eq_length (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  haveI : IsNoetherian (TowerStage A t p n) V :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hV).1
  rw [towerLengthFun_eq_fgLength_of_noetherian A t p ht,
    fgLength_tensor A t p ht n V hV]

/-- 有限段の通常の長さの加法性から、根の塔へ係数拡大した加群の生の長さの加法性を導く。
中央の加群が有限長であることだけで、両端の有限長性も従う。 -/
theorem towerLengthFun_add_of_stage_exact (n : ℕ) (V₁ V₂ V₃ : Type u)
    [AddCommGroup V₁] [Module (TowerStage A t p n) V₁]
    [AddCommGroup V₂] [Module (TowerStage A t p n) V₂]
    [AddCommGroup V₃] [Module (TowerStage A t p n) V₃]
    (f : V₁ →ₗ[TowerStage A t p n] V₂) (g : V₂ →ₗ[TowerStage A t p n] V₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hV₂ : IsFiniteLength (TowerStage A t p n) V₂) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V₂) =
      towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V₁) +
      towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V₃) := by
  have hV₁ : IsFiniteLength (TowerStage A t p n) V₁ :=
    IsFiniteLength.of_injective hV₂ hf
  have hV₃ : IsFiniteLength (TowerStage A t p n) V₃ :=
    IsFiniteLength.of_surjective hV₂ hg
  rw [towerLengthFun_tensor_eq_length A t p ht n V₁ hV₁,
    towerLengthFun_tensor_eq_length A t p ht n V₂ hV₂,
    towerLengthFun_tensor_eq_length A t p ht n V₃ hV₃,
    Module.length_eq_add_of_exact f g hf hg hfg, ENat.toENNReal_add, ENNReal.add_div]

omit [IsNoetherianRing A] in
/-- 有限段からの係数拡大の中の有限生成部分加群とその商を、
共通の有限段の部分加群と商として実現する。 -/
theorem exists_stage_submodule_and_quotient_equiv (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module (TowerStage A t p n) V]
    (hV : IsFiniteLength (TowerStage A t p n) V)
    (N : Submodule (Tower A t p) (Tower A t p ⊗[TowerStage A t p n] V)) (hN : N.FG) :
    ∃ (k : ℕ) (hnk : n ≤ k),
      letI := (towerMap A t p n k hnk).toRingHom.toAlgebra
      letI := isScalarTower_towerMap_tower A t p n k hnk
      ∃ K : Submodule (TowerStage A t p k)
          (TowerStage A t p k ⊗[TowerStage A t p n] V),
        IsFiniteLength (TowerStage A t p k)
            (TowerStage A t p k ⊗[TowerStage A t p n] V) ∧
          Nonempty (Tower A t p ⊗[TowerStage A t p k] K ≃ₗ[Tower A t p] N) ∧
          Nonempty (Tower A t p ⊗[TowerStage A t p k]
            ((TowerStage A t p k ⊗[TowerStage A t p n] V) ⧸ K) ≃ₗ[Tower A t p]
              ((Tower A t p ⊗[TowerStage A t p n] V) ⧸ N)) := by
  classical
  haveI : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
  obtain ⟨r, z, hz⟩ := Module.Finite.exists_fin (R := Tower A t p) (M := N)
  obtain ⟨k, hnk, w, hw⟩ := exists_tower_tensor_family_stage A t p n V (fun j ↦ (z j).val)
  letI := (towerMap A t p n k hnk).toRingHom.toAlgebra
  letI := isScalarTower_towerMap_tower A t p n k hnk
  let Q := TowerStage A t p k ⊗[TowerStage A t p n] V
  let M := Tower A t p ⊗[TowerStage A t p n] V
  let K : Submodule (TowerStage A t p k) Q := Submodule.span _ (Set.range w)
  let E := TensorProduct.AlgebraTensorModule.cancelBaseChange (TowerStage A t p n)
    (TowerStage A t p k) (Tower A t p) (Tower A t p) V
  let F : Q →ₗ[TowerStage A t p k] M :=
    (E.toLinearMap.restrictScalars (TowerStage A t p k)).comp
      (TensorProduct.mk (TowerStage A t p k) (Tower A t p) Q 1)
  have hF : K ≤ (N.restrictScalars (TowerStage A t p k)).comap F := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change E (1 ⊗ₜ w j) ∈ N
    rw [hw j]
    exact (z j).property
  let FK : K →ₗ[TowerStage A t p k] N :=
    { toFun := fun x ↦ ⟨F x, hF x.property⟩
      map_add' := fun x y ↦ Subtype.ext (F.map_add x y)
      map_smul' := fun a x ↦ Subtype.ext (F.map_smul a x) }
  let L := FK.liftBaseChange (Tower A t p)
  have hLs : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hz, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨1 ⊗ₜ (⟨w j, Submodule.subset_span (Set.mem_range_self j)⟩ : K), ?_⟩
    apply Subtype.ext
    change (1 : Tower A t p) • E (1 ⊗ₜ w j) = (z j).val
    rw [one_smul, hw j]
  let B := K.subtype.baseChange (Tower A t p)
  have hcomm : N.subtype.comp L = E.toLinearMap.comp B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change a • E (1 ⊗ₜ (x : Q)) = E (a ⊗ₜ (x : Q))
    rw [← E.map_smul]
    congr 1
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  letI := flat_tower A t p k
  have hBi : Function.Injective B :=
    Module.Flat.lTensor_preserves_injective_linearMap K.subtype (Submodule.subtype_injective K)
  have hLi : Function.Injective L := by
    have hc : Function.Injective (N.subtype.comp L) := hcomm.symm ▸ E.injective.comp hBi
    intro x y hxy
    exact hc (congrArg (fun v : N ↦ v.val) hxy)
  let π := N.mkQ.comp E.toLinearMap
  have hπs : Function.Surjective π := N.mkQ_surjective.comp E.surjective
  have hπ : Function.Exact B π := by
    rw [LinearMap.exact_iff]
    ext x
    change π x = 0 ↔ x ∈ LinearMap.range B
    change N.mkQ (E x) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hLs ⟨E x, hx⟩
      refine ⟨y, E.injective ?_⟩
      have hc := LinearMap.congr_fun hcomm y
      exact hc.symm.trans (congrArg (fun v : N ↦ v.val) hy)
    · rintro ⟨y, rfl⟩
      have hc := LinearMap.congr_fun hcomm y
      change (L y).val = E (B y) at hc
      rw [← hc]
      exact (L y).property
  let S := K.mkQ.baseChange (Tower A t p)
  have hSs : Function.Surjective S := LinearMap.lTensor_surjective _ K.mkQ_surjective
  have hS₀ := _root_.lTensor_exact (R := TowerStage A t p k) (M := K) (N := Q)
    (P := Q ⧸ K) (f := K.subtype) (g := K.mkQ) (Tower A t p)
    (LinearMap.exact_subtype_mkQ K) K.mkQ_surjective
  have hS : Function.Exact B S := hS₀
  have hker : S.ker = π.ker := hS.linearMap_ker_eq.trans hπ.linearMap_ker_eq.symm
  let eQuot := (S.quotKerEquivOfSurjective hSs).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (π.quotKerEquivOfSurjective hπs))
  have hQ : IsFiniteLength (TowerStage A t p k) Q := by
    rw [← Module.length_ne_top_iff]
    change Module.length (TowerStage A t p k)
      (TowerStage A t p k ⊗[TowerStage A t p n] V) ≠ ⊤
    rw [length_tensor_towerMap A t p n k hnk ht]
    obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top_iff.mpr hV)
    rw [← hl, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  exact ⟨k, hnk, K, hQ, ⟨LinearEquiv.ofBijective L ⟨hLi, hLs⟩⟩, ⟨eQuot⟩⟩

/-- 有限表示な冪ねじれ加群とその有限生成部分加群・商について、生の長さは加法的。
共通の有限段の部分加群の短完全列に帰着する。 -/
theorem towerLengthFun_add_submodule_of_finitePresentation (M : Type u)
    [AddCommGroup M] [Module (Tower A t p) M]
    [Module.FinitePresentation (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M)
    (N : Submodule (Tower A t p) M) (hN : N.FG) :
    towerLengthFun A t p M = towerLengthFun A t p N + towerLengthFun A t p (M ⧸ N) := by
  obtain ⟨n, V, i₁, i₂, hV, _, ⟨e⟩⟩ := exists_descent A t p M hM
  let N' := N.map e.toLinearMap
  obtain ⟨k, hnk, K, hQ, ⟨eK⟩, ⟨eQuot⟩⟩ :=
    exists_stage_submodule_and_quotient_equiv A t p ht n V hV N' (hN.map e.toLinearMap)
  letI := (towerMap A t p n k hnk).toRingHom.toAlgebra
  letI := isScalarTower_towerMap_tower A t p n k hnk
  let Q := TowerStage A t p k ⊗[TowerStage A t p n] V
  let E := TensorProduct.AlgebraTensorModule.cancelBaseChange (TowerStage A t p n)
    (TowerStage A t p k) (Tower A t p) (Tower A t p) V
  let eN : N ≃ₗ[Tower A t p] N' :=
    Submodule.equivMapOfInjective e.toLinearMap e.injective N
  let eMQ : (M ⧸ N) ≃ₗ[Tower A t p]
      ((Tower A t p ⊗[TowerStage A t p n] V) ⧸ N') :=
    Submodule.Quotient.equiv N N' e rfl
  have hleft := towerLengthFun_congr (A := A) (t := t) (p := p) (eK.trans eN.symm)
  have hright := towerLengthFun_congr (A := A) (t := t) (p := p) (eQuot.trans eMQ.symm)
  calc
    towerLengthFun A t p M = towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p k] Q) :=
      (towerLengthFun_congr (E.trans e.symm)).symm
    _ = towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p k] K) +
        towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p k] (Q ⧸ K)) :=
      towerLengthFun_add_of_stage_exact A t p ht k K Q (Q ⧸ K) K.subtype K.mkQ
        (Submodule.subtype_injective K) K.mkQ_surjective (LinearMap.exact_subtype_mkQ K) hQ
    _ = towerLengthFun A t p N + towerLengthFun A t p (M ⧸ N) := by
      rw [hleft, hright]

end SerrePositivity.Section2

end AdditivityFinitePart

section AdditivityFinitelyGeneratedPart

set_option linter.style.haveILetI false

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

end AdditivityFinitelyGeneratedPart

section NormalizedPart

namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing
open scoped ENNReal

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)

/-- 有限段の長さと近似から証明した法則を持つ、具体的な根の塔の正規化長さ。
基底と座標の仮定を明示し、加法性を文献の引用で埋めない。 -/
noncomputable def normalizedLength :
    NormalizedLength (Tower A t p) (towerMaxIdeal A t p) where
  len M _ _ := towerLengthFun A t p M
  len_eq_zero_of_subsingleton M _ _ _ := towerLengthFun_eq_zero_of_subsingleton M
  len_congr _ _ _ _ _ _ e := towerLengthFun_congr e
  len_add_of_exact _ _ _ _ _ _ _ _ _ f g hf hg hfg hM :=
    towerLengthFun_add_of_exact_of_noetherian A t p ht f g hf hg hfg hM

/-- 新しい正規化長さの値は既存の三段階の数値関数と定義上同じ。 -/
@[simp] theorem normalizedLength_len (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] :
    (normalizedLength A t p ht).len M = towerLengthFun A t p M := rfl

/-- 証明した有限生成一致から、正規化長さの上限の性質を供給する。
長さの構造そのものも、その性質の証明も未証明の C2 に依存しない。 -/
theorem normalizedLength_hasSup : (normalizedLength A t p ht).HasSup := by
  intro M _ _ hM
  rw [normalizedLength_len, towerLengthFun]
  refine le_antisymm (iSup₂_le fun N hN ↦ le_iSup₂_of_le N hN (le_of_eq ?_))
    (iSup₂_le fun N hN ↦ le_iSup₂_of_le N hN (le_of_eq ?_))
  · have : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
    rw [normalizedLength_len, towerLengthFun_eq_fgLength_of_noetherian A t p ht N]
  · have : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
    rw [normalizedLength_len, towerLengthFun_eq_fgLength_of_noetherian A t p ht N]

end SerrePositivity.RootTowerLength

end NormalizedPart
