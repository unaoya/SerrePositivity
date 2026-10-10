module

public import SerrePositivity.Paper.Section2.PerfectBaseChange
public import SerrePositivity.CommutativeAlgebra.TraceConductor

/-!
# 共通分母の Frobenius 根への移行

完全な係数環 `R` 上の近似部分代数 `B_q = R D^(1/q)` を考える。
逆 Frobenius は `B_1` を `B_q` に送る。したがって `g C ⊆ B_1` なら
`g^(1/q) C ⊆ B_q` であり、既存の商の核の長さ評価に使える。
一般形では最初の共通分母の存在と `R` の完全性を明示的な前提とする。
論文の設定では `Tower ≃+* PerfectClosure A p` を構成して塔の完全性を証明し、
完全性を追加仮定にせず各段の包含を導く。
基底環の正規性を明示的に仮定した場合は、分数体上のトレースの議論を適用し、
最初の分母の存在から全ての段の包含までを導く。
-/

public section
universe u
namespace SerrePositivity.Section2

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (R : Type u) [CommRing R] [Algebra R (PerfectClosure D p)] [PerfectRing R p]

/-- 完全な係数環上では、初段の近似部分代数の `pⁿ` 乗根は第 `n` 段に入る。
生成元は `D` の根になり、係数の根は係数環の完全性から再び係数環に入る。 -/
theorem perfectionApproximation_root_mem (n : ℕ) {x : PerfectClosure D p}
    (hx : x ∈ perfectionApproximation D p R 0) :
    (iterateFrobeniusEquiv (PerfectClosure D p) p n).symm x ∈
      perfectionApproximation D p R n := by
  let e := iterateFrobeniusEquiv (PerfectClosure D p) p n
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      have he : e.symm (perfectionRootHom D p 0 d) = perfectionRootHom D p n d := by
        apply e.injective
        rw [RingEquiv.apply_symm_apply]
        change perfectionRootHom D p 0 d = perfectionRootHom D p n d ^ (p ^ n)
        rw [perfectionRootHom_apply, perfectionRootHom_apply, perfection_mk_pow]
        rfl
      rw [he]
      exact Algebra.subset_adjoin (Set.mem_range_self d)
  | algebraMap r =>
      obtain ⟨s, hs⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p ^ n)).surjective r
      change s ^ (p ^ n) = r at hs
      have he : e.symm (algebraMap R (PerfectClosure D p) r) =
          algebraMap R (PerfectClosure D p) s := by
        apply e.injective
        rw [RingEquiv.apply_symm_apply]
        change algebraMap R (PerfectClosure D p) r =
          algebraMap R (PerfectClosure D p) s ^ (p ^ n)
        rw [← map_pow, hs]
      rw [he]
      exact Subalgebra.algebraMap_mem _ s
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ ihx ihy

/-- 一つの共通分母から、全ての近似段の共通分母を得る。
`C` の任意の元の `pⁿ` 乗に初段の包含を適用し、逆 Frobenius を取る。 -/
theorem perfectionApproximation_conductor_root (g : D)
    (hg : ∀ c : PerfectClosure D p, PerfectClosure.of D p g * c ∈
      perfectionApproximation D p R 0) (n : ℕ) (c : PerfectClosure D p) :
    perfectionRootHom D p n g * c ∈ perfectionApproximation D p R n := by
  let e := iterateFrobeniusEquiv (PerfectClosure D p) p n
  have hm := perfectionApproximation_root_mem D p R n (hg (c ^ (p ^ n)))
  have he : e.symm (PerfectClosure.of D p g) = perfectionRootHom D p n g := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    change PerfectClosure.of D p g = perfectionRootHom D p n g ^ (p ^ n)
    rw [perfectionRootHom_apply, perfection_mk_pow]
  change e.symm (PerfectClosure.of D p g * e c) ∈ _ at hm
  rw [map_mul, he, RingEquiv.symm_apply_apply] at hm
  exact hm

/-- 初段の共通分母だけから、各段の商への写像の核を分母の根を加えた商で評価する。
各段ごとに共通分母条件を仮定し直す必要はない。 -/
theorem perfectionApproximation_kernel_bound_of_conductor
    {J : Ideal R} (lam : NormalizedLength R J) (g : D)
    (hg : ∀ c : PerfectClosure D p, PerfectClosure.of D p g * c ∈
      perfectionApproximation D p R 0)
    (n : ℕ) (I : Ideal (perfectionApproximation D p R n))
    (htors : IsPowTorsion J ((perfectionApproximation D p R n) ⧸ I))
    (hfinite : lam.len ((perfectionApproximation D p R n) ⧸ I) ≠ ⊤) :
    lam.len (LinearMap.ker
      ((quotientToExtension (C := PerfectClosure D p) I).toLinearMap.restrictScalars R)) ≤
    lam.len ((perfectionApproximation D p R n) ⧸
      (I ⊔ Ideal.span {⟨perfectionRootHom D p n g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩})) := by
  apply perfectionApproximation_kernel_bound D p R lam n I _ _ htors hfinite
  exact perfectionApproximation_conductor_root D p R g hg n

/-- 等標数で完全な剰余体を持つ完備正則局所環の根の塔は、その perfection と同型。
各段の Frobenius の全射性から、塔の像が基底環の perfection 全体になる。
単射性には既存の正則パラメータの入力から得る各段の被約性を使う。 -/
noncomputable def towerEquivPerfection
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharP A p]
    [CharP (IsLocalRing.ResidueField A) p] [PerfectRing (IsLocalRing.ResidueField A) p]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) : Tower A t p ≃+* PerfectClosure A p := by
  let := isDomain_of_isRegularLocalRing A
  let : Algebra A (PerfectClosure A p) := (PerfectClosure.of A p).toAlgebra
  have hchar (n : ℕ) : CharP (TowerStage A t p n) p := by
    let := isRegularLocalRing_towerStage A t p ht hdim n
    let := towerStage_free A t p n
    exact charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective A _) p
  have hred (n : ℕ) : IsReduced (TowerStage A t p n) := by
    let := isRegularLocalRing_towerStage A t p ht hdim n
    let := isDomain_of_isRegularLocalRing (TowerStage A t p n)
    infer_instance
  let f := towerToPerfect A (PerfectClosure A p) t p
  have hfi : Function.Injective f := towerToPerfect_injective A (PerfectClosure A p) t p
    hchar hred (by
      intro a b hab
      change PerfectClosure.of A p a = PerfectClosure.of A p b at hab
      apply perfectionRootHom_injective A p 0
      simpa only [perfectionRootHom_apply, PerfectClosure.of_apply] using hab)
  have hfs : Function.Surjective f := by
    intro c
    induction c using PerfectClosure.induction_on with
    | h c =>
        obtain ⟨x, hx⟩ := towerStageFrobenius_surjective A t p ht c.1 c.2
        refine ⟨towerOf A t p c.1 x, ?_⟩
        let := hchar c.1
        apply (iterateFrobeniusEquiv (PerfectClosure A p) p c.1).injective
        change f (towerOf A t p c.1 x) ^ (p ^ c.1) =
          PerfectClosure.mk A p c ^ (p ^ c.1)
        rw [perfection_mk_pow]
        change towerToPerfect A (PerfectClosure A p) t p (towerOf A t p c.1 x) ^ (p ^ c.1) = _
        rw [towerToPerfect_of]
        rw [← map_pow, ← towerStageFrobenius_pow, AlgHom.commutes, hx]
        rfl
  exact RingEquiv.ofBijective f.toRingHom ⟨hfi, hfs⟩

/-- 塔と perfection の環同型から、塔の Frobenius が全単射であることを導く。 -/
theorem perfectRing_tower
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharP A p]
    [CharP (IsLocalRing.ResidueField A) p] [PerfectRing (IsLocalRing.ResidueField A) p]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) : PerfectRing (Tower A t p) p := by
  let e := towerEquivPerfection p A t ht hdim
  constructor
  constructor
  · intro x y hxy
    apply e.injective
    apply (PerfectRing.bijective_frobenius (R := PerfectClosure A p) (p := p)).injective
    simpa only [map_pow] using congrArg e hxy
  · intro x
    obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius
      (R := PerfectClosure A p) (p := p)).surjective (e x)
    obtain ⟨z, hz⟩ := e.surjective y
    refine ⟨z, e.injective ?_⟩
    simpa only [map_pow, hz] using hy

/-- 正規な基底環から作った等標数の塔は正規である。
塔と perfection の同型に沿って、perfection の正規性を移す。
`A` の正規性を正則性から導く主張とは分け、必要な前提を明示する。 -/
theorem isIntegrallyClosed_tower_of_base
    (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharP A p]
    [CharP (IsLocalRing.ResidueField A) p] [PerfectRing (IsLocalRing.ResidueField A) p]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) : IsIntegrallyClosed (Tower A t p) := by
  let := isDomain_of_isRegularLocalRing A
  let := perfectClosure_isIntegrallyClosed A p
  exact IsIntegrallyClosed.of_equiv (towerEquivPerfection p A t ht hdim).symm

attribute [local instance] towerPerfectionAlgebra

/-- 論文の塔上で、初段の共通分母から全ての段の共通分母を得る。
塔の完全性はここで証明して用い、追加の仮定にはしない。 -/
theorem tower_perfectionApproximation_conductor_root
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsLocalRing D] [Algebra A D] [Algebra A (PerfectClosure D p)]
    [CharP (IsLocalRing.ResidueField D) p] [PerfectField (IsLocalRing.ResidueField D)]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap A D)))
    (g : D) (hg : ∀ c : PerfectClosure D p, PerfectClosure.of D p g * c ∈
      perfectionApproximation D p (Tower A t p) 0)
    (n : ℕ) (c : PerfectClosure D p) :
    perfectionRootHom D p n g * c ∈ perfectionApproximation D p (Tower A t p) n := by
  let : CharP A p := (algebraMap A D).charP hinj p
  let er := residueFieldEquiv_of_surjective (R := A) D hres
  let : CharP (IsLocalRing.ResidueField A) p := er.toRingHom.charP er.injective p
  let : PerfectField (IsLocalRing.ResidueField A) := PerfectField.of_ringEquiv er.symm
  let := perfectRing_tower p A t ht hdim
  exact perfectionApproximation_conductor_root D p (Tower A t p) g hg n c

section InitialConductor
attribute [local instance] FractionRing.liftAlgebra

/-- 正規な基底環から作った塔では、perfection 全体を初段の近似部分代数に送る
非零の共通分母を基底環内に選べる。有限拡大の生成的分離性、塔の純非分離性と
完全性を分数体上で組み合わせ、トレースによる共通分母を環に引き戻す。
基底環の正規性は明示的な前提であり、正則性からの導出はこの補題に含めない。 -/
theorem exists_tower_perfection_conductor_of_normal_base
    (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsDomain D] [Algebra A D] [Module.Finite A D]
    [Algebra A (PerfectClosure D p)]
    [CharP (IsLocalRing.ResidueField A) p] [PerfectRing (IsLocalRing.ResidueField A) p]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) (hinj : Function.Injective (algebraMap A D))
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) :
    ∃ g : A, g ≠ 0 ∧ ∀ c : PerfectClosure D p,
      PerfectClosure.of D p (algebraMap A D g) * c ∈
        perfectionApproximation D p (Tower A t p) 0 := by
  let C := PerfectClosure D p
  let R := Tower A t p
  let := perfectClosure_isDomain D p
  let := isDomain_of_isRegularLocalRing A
  let : CharP A p := (algebraMap A D).charP hinj p
  let : Algebra D C := (PerfectClosure.of D p).toAlgebra
  let : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq hbase
  let : IsScalarTower A R C := IsScalarTower.of_algebraMap_eq fun a ↦
    ((towerToPerfect A C t p).commutes a).symm
  have hof : Function.Injective (PerfectClosure.of D p) := fun x y hxy ↦
    (PerfectClosure.eq_iff D p (0, x) (0, y)).mp hxy
  have hAC : Function.Injective (algebraMap A C) := by
    intro a b hab
    change algebraMap A (PerfectClosure D p) a = algebraMap A (PerfectClosure D p) b at hab
    exact hinj (hof (by simpa only [hbase] using hab))
  have hRC := towerToPerfection_injective_of_regular A D p t ht hdim hAC
  let : IsDomain R := Function.Injective.isDomain
    (towerToPerfect A C t p).toRingHom hRC
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  let : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hAC
  let : FaithfulSMul D C := (faithfulSMul_iff_algebraMap_injective D C).mpr hof
  let : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hRC
  let : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr
    (fun x y hxy ↦ hAC (by
      rw [IsScalarTower.algebraMap_apply A R C, IsScalarTower.algebraMap_apply A R C, hxy]))
  let := perfectRing_tower p A t ht hdim
  let := isIntegrallyClosed_tower_of_base p A t ht hdim
  let K := FractionRing A
  let E := FractionRing R
  let L := FractionRing D
  let Ω := FractionRing C
  let : CharP R p := charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective A R) p
  let : PerfectRing E p := perfectRing_fractionRing R E p
  let : PerfectField E := PerfectRing.toPerfectField E p
  have hchar (n : ℕ) : CharP (TowerStage A t p n) p := by
    let := isRegularLocalRing_towerStage A t p ht hdim n
    let := towerStage_free A t p n
    exact charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective A _) p
  let : IsPurelyInseparable K E := by
    apply isPurelyInseparable_fractionRing_of_pow_mem R K E p
    intro r
    obtain ⟨n, a, ha⟩ := tower_pow_mem_range A t p hchar r
    refine ⟨n, algebraMap A K a, ?_⟩
    rw [← IsScalarTower.algebraMap_apply A K E,
      IsScalarTower.algebraMap_apply A R E, ha, map_pow]
  let : Algebra.IsSeparable K L := isSeparable_fractionRing_of_separable_minpoly A D K L hsep
  let : IsPurelyInseparable L Ω :=
    perfectClosure_fractionRing_isPurelyInseparable D p L Ω (fun _ ↦ rfl)
  let : Algebra.IsIntegral A C := ⟨isIntegral_perfection_of_isIntegral D p A hbase⟩
  let : Algebra.IsAlgebraic C Ω := IsLocalization.isAlgebraic Ω (nonZeroDivisors C)
  let : Algebra.IsAlgebraic A Ω := Algebra.IsAlgebraic.trans A C Ω
  let f := IsScalarTower.toAlgHom R C Ω
  let B := perfectionApproximation D p R 0
  have hD (d : D) : algebraMap D Ω d ∈ B.map f := by
    apply Subalgebra.mem_map.mpr
    refine ⟨PerfectClosure.of D p d, ?_, ?_⟩
    · have hd := Algebra.subset_adjoin (R := R)
        (Set.mem_range_self (f := perfectionRootHom D p 0) d)
      simpa only [B, perfectionApproximation, perfectionRootHom_apply, PerfectClosure.of_apply,
        SetLike.mem_coe] using hd
    · exact (IsScalarTower.algebraMap_apply D C Ω d).symm
  have hC : ∀ x ∈ f.range, IsIntegral R x := by
    rintro _ ⟨c, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := A) c).tower_top).map f
  obtain ⟨g, hg, hgc⟩ := exists_smul_subalgebra_le_of_fractionRing
    A D R K E L Ω p (B.map f) f.range hD hC
  refine ⟨g, hg, fun c ↦ ?_⟩
  obtain ⟨b, hb, he⟩ := Subalgebra.mem_map.mp (hgc (f c) ⟨c, rfl⟩)
  have heq : b = PerfectClosure.of D p (algebraMap A D g) * c := by
    apply IsFractionRing.injective C Ω
    change f b = f (PerfectClosure.of D p (algebraMap A D g) * c)
    rw [he, map_mul, Algebra.smul_def, ← hbase,
      IsScalarTower.algebraMap_apply A C Ω]
    rfl
  exact heq ▸ hb

/-- 正規な基底環の設定では、一つの非零元を選ぶだけで全ての近似段の
共通分母が得られる。選んだ元の `pⁿ` 乗根が第 `n` 段の分母となるため、
後の核の長さ評価では各段の分母の存在を仮定する必要がない。 -/
theorem exists_tower_perfection_conductor_roots_of_normal_base
    (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsDomain D] [Algebra A D] [Module.Finite A D]
    [Algebra A (PerfectClosure D p)]
    [CharP (IsLocalRing.ResidueField A) p] [PerfectRing (IsLocalRing.ResidueField A) p]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) (hinj : Function.Injective (algebraMap A D))
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) :
    ∃ g : A, g ≠ 0 ∧ ∀ n : ℕ, ∀ c : PerfectClosure D p,
      perfectionRootHom D p n (algebraMap A D g) * c ∈
        perfectionApproximation D p (Tower A t p) n := by
  obtain ⟨g, hg, hgc⟩ := exists_tower_perfection_conductor_of_normal_base
    D p A t ht hdim hinj hbase hsep
  let : CharP A p := (algebraMap A D).charP hinj p
  let := perfectRing_tower p A t ht hdim
  exact ⟨g, hg, perfectionApproximation_conductor_root D p (Tower A t p)
    (algebraMap A D g) hgc⟩

end InitialConductor

end SerrePositivity.Section2
