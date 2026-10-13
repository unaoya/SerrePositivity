module

public import SerrePositivity.LengthAlgebra.RootTowerLength.FiniteGeneration
public import Mathlib.Algebra.Module.Projective

/-!
# 有限生成部分加群による長さの近似

三つの数値関数と証明済みの有限生成一致だけから、一般の `λ∞` の単調性と
有限生成部分加群による近似を示す。加法性への還元では、必要な有限生成・
有限表示の補題を定理の明示引数として受け取り、未証明の構造体や引用は導入しない。
`towerLength` の構造や C2 の引用には依存しない。
-/

@[expose] public noncomputable section

universe u v

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

/-- 有向な部分加群の上限に入る有限生成部分加群は、一つの段に既に入る。 -/
theorem exists_le_directed_family_of_fg
    {M : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    {ι : Type v} [Nonempty ι] (F : ι → Submodule (Tower A t p) M)
    (hF : Directed (· ≤ ·) F) (S : Submodule (Tower A t p) M) (hS : S.FG)
    (hSF : S ≤ iSup F) : ∃ i, S ≤ F i := by
  have hdir : DirectedOn (· ≤ ·) (Set.range F) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hF i j
    exact ⟨F k, Set.mem_range_self k, hik, hjk⟩
  have hsup : S ≤ sSup (Set.range F) := by simpa only [sSup_range] using hSF
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ :=
    (isCompactElement_iff_le_of_directed_sSup_le S).mp
      ((Submodule.fg_iff_compact S).mp hS) (Set.range F) (Set.range_nonempty F) hdir hsup
  exact ⟨i, hi⟩

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

include ht in
/-- 有向な部分加群の合併では、生の `λ∞` は各段の値の上限。
有限生成一致と、有限生成部分加群が一つの段に入ることから従う。 -/
theorem towerLengthFun_iSup_of_directed
    {M : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    {ι : Type v} [Nonempty ι] (F : ι → Submodule (Tower A t p) M)
    (hF : Directed (· ≤ ·) F) :
    towerLengthFun A t p ↥(iSup F) = ⨆ i, towerLengthFun A t p (F i) := by
  let T : Submodule (Tower A t p) M := iSup F
  apply le_antisymm
  · apply iSup₂_le
    intro S hS
    have hST : S.map T.subtype ≤ T := by
      rintro _ ⟨x, hx, rfl⟩
      exact x.2
    obtain ⟨i, hi⟩ := exists_le_directed_family_of_fg A t p F hF (S.map T.subtype)
      (hS.map T.subtype) hST
    let f : S →ₗ[Tower A t p] F i :=
      { toFun := fun x => ⟨x.1.1, hi (Submodule.mem_map.mpr ⟨x.1, x.2, rfl⟩)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x y hxy
      have hval := congrArg (fun z : F i => (z : M)) hxy
      change x.1.1 = y.1.1 at hval
      exact Subtype.ext (Subtype.ext hval)
    let : Module.Finite (Tower A t p) S := Module.Finite.iff_fg.mpr hS
    rw [← towerLengthFun_eq_fgLength_of_noetherian A t p ht S]
    exact (towerLengthFun_le_of_injective A t p f hf).trans
      (le_iSup (fun i => towerLengthFun A t p (F i)) i)
  · apply iSup_le
    intro i
    exact towerLengthFun_le_of_injective A t p
      (Submodule.inclusion (le_iSup F i)) (Submodule.inclusion_injective _)

include ht in
/-- 合併が全加群である有向部分加群族でも、長さは段の値の上限。 -/
theorem towerLengthFun_eq_iSup_of_directed_union
    {M : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    {ι : Type v} [Nonempty ι] (F : ι → Submodule (Tower A t p) M)
    (hF : Directed (· ≤ ·) F) (hunion : iSup F = ⊤) :
    towerLengthFun A t p M = ⨆ i, towerLengthFun A t p (F i) := by
  have h := towerLengthFun_iSup_of_directed A t p ht F hF
  rw [hunion] at h
  exact (towerLengthFun_congr (Submodule.topEquiv :
    (⊤ : Submodule (Tower A t p) M) ≃ₗ[Tower A t p] M)).symm.trans h

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

include ht in
/-- 有限生成の三項の短完全列で加法性が証明されれば、一般の短完全列でも加法性が従う。
有限表示から有限生成への接続はこの明示引数の定理として渡し、引用や構造体には隠さない。 -/
theorem towerLengthFun_add_of_exact_of_finitelyGeneratedExact
    (hfgexact : ∀ (L M N : Type u)
      [AddCommGroup L] [Module (Tower A t p) L] [Module.Finite (Tower A t p) L]
      [AddCommGroup M] [Module (Tower A t p) M] [Module.Finite (Tower A t p) M]
      [AddCommGroup N] [Module (Tower A t p) N] [Module.Finite (Tower A t p) N]
      (f : L →ₗ[Tower A t p] M) (g : M →ₗ[Tower A t p] N),
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      IsPowTorsion (towerMaxIdeal A t p) M →
      towerLengthFun A t p M = towerLengthFun A t p L + towerLengthFun A t p N)
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module (Tower A t p) M₁]
    [AddCommGroup M₂] [Module (Tower A t p) M₂]
    [AddCommGroup M₃] [Module (Tower A t p) M₃]
    (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂) :
    towerLengthFun A t p M₂ = towerLengthFun A t p M₁ + towerLengthFun A t p M₃ := by
  apply towerLengthFun_add_of_exact_of_fg_additivity A t p ht ?_ f g hf hg hfg hM₂
  intro M _ _ _ K hK hM
  let : Module.Finite (Tower A t p) K := Module.Finite.iff_fg.mpr hK
  exact hfgexact K M (M ⧸ K) K.subtype K.mkQ K.subtype_injective K.mkQ_surjective
    (LinearMap.exact_subtype_mkQ K) hM

end SerrePositivity.Section2
