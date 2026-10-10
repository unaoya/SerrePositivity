module

public import SerrePositivity.Paper.Section2.PerfectTower
public import SerrePositivity.PerfectComplex.QuotientLength
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.CharP.Algebra
public import SerrePositivity.CommutativeAlgebra.PerfectNormality

/-!
# Perfection の部分代数による近似

`D_perf` の中で `D^{1/pⁿ}` と係数環 `R` が生成する部分代数を定義する。
これらは増大し、全ての元を覆う。定理2.5では `R = Λ` として `B_q` の像を扱う。
共通分母を与えれば、商への写像の核の長さを分母倍写像の余核の長さで評価できる。
テンソル積表示との同定は `PerfectBaseChange.lean` で証明する。
近似環の商の正規化長さは `PerfectApproximationLength.lean` で証明する。
固定した商の中での像も定義し、その増大性と被覆を証明する。
共通分母の一般論は `TraceConductor.lean` にあり、正規な基底を仮定した塔への適用は
`PerfectConductor.lean` で証明済み。
-/

public section
universe u
namespace SerrePositivity.Section2

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]

/-- `D` の元をその `pⁿ` 乗根に送る、perfection への環準同型。 -/
noncomputable def perfectionRootHom (n : ℕ) : D →+* PerfectClosure D p :=
  (iterateFrobeniusEquiv (PerfectClosure D p) p n).symm.toRingHom.comp
    (PerfectClosure.of D p)

/-- 商による perfection の表示で、段 `n` の元の `pⁿ` 乗は元の環に戻る。 -/
theorem perfection_mk_pow (n : ℕ) (x : D) :
    PerfectClosure.mk D p (n, x) ^ (p ^ n) = PerfectClosure.of D p x := by
  induction n with
  | zero => rw [pow_zero, pow_one, PerfectClosure.of_apply]
  | succ n ih =>
      rw [pow_succ', pow_mul, PerfectClosure.mk_pow, PerfectClosure.mk_succ_pow, ih]

/-- 逆 Frobenius による根は、Mathlib の perfection の段の表示と一致する。 -/
theorem perfectionRootHom_apply (n : ℕ) (x : D) :
    perfectionRootHom D p n x = PerfectClosure.mk D p (n, x) := by
  apply (iterateFrobeniusEquiv (PerfectClosure D p) p n).injective
  change (iterateFrobeniusEquiv (PerfectClosure D p) p n)
    ((iterateFrobeniusEquiv (PerfectClosure D p) p n).symm (PerfectClosure.of D p x)) = _
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, perfection_mk_pow]

/-- 被約環では、各段への根の写像は単射である。 -/
theorem perfectionRootHom_injective [IsReduced D] (n : ℕ) :
    Function.Injective (perfectionRootHom D p n) := by
  intro x y hxy
  rw [perfectionRootHom_apply, perfectionRootHom_apply] at hxy
  obtain ⟨k, hk⟩ := (PerfectClosure.mk_eq_iff D p (n, x) (n, y)).mp hxy
  exact ((frobenius_inj D p).iterate (n + k)) hk

/-- 単射な環準同型を完全環へ延長しても単射である。
核の元の十分大きい Frobenius 冪を元の環に戻して判定する。 -/
theorem perfectClosure_lift_injective (C : Type u) [CommRing C] [CharP C p]
    [PerfectRing C p] (f : D →+* C) (hf : Function.Injective f) :
    Function.Injective (PerfectClosure.lift D p C f) := by
  let g := PerfectClosure.lift D p C f
  have hcomp : g.comp (PerfectClosure.of D p) = f :=
    (PerfectClosure.lift D p C).symm_apply_apply f
  apply (injective_iff_map_eq_zero g).mpr
  intro x hx
  induction x using PerfectClosure.induction_on with
  | h x =>
    obtain ⟨n, a⟩ := x
    have ha : f a = 0 := by
      rw [← RingHom.congr_fun hcomp a]
      change g (PerfectClosure.of D p a) = 0
      rw [← perfection_mk_pow D p n a, map_pow, hx,
        zero_pow (pow_pos (Fact.out : p.Prime).pos n).ne']
    have ha0 : a = 0 := hf (ha.trans (map_zero _).symm)
    rw [← perfectionRootHom_apply, ha0, map_zero]

/-- 整域の perfection は整域。分数体の perfection への単射で示す。 -/
theorem perfectClosure_isDomain [IsDomain D] : IsDomain (PerfectClosure D p) := by
  let : CharP (FractionRing D) p :=
    charP_of_injective_algebraMap (IsFractionRing.injective D _) p
  let f := (PerfectClosure.of (FractionRing D) p).comp (algebraMap D (FractionRing D))
  have hf : Function.Injective f :=
    (PerfectClosure.of (FractionRing D) p).injective.comp (IsFractionRing.injective D _)
  exact Function.Injective.isDomain (PerfectClosure.lift D p (PerfectClosure (FractionRing D) p) f)
    (perfectClosure_lift_injective D p _ f hf)

/-- Perfection の中の根の段 `D^{1/pⁿ}`。 -/
noncomputable abbrev perfectionRootStage (n : ℕ) : Subring (PerfectClosure D p) :=
  (perfectionRootHom D p n).range

/-- 根の段は元の被約環と環同型である。順写像は根を取り、逆写像は `pⁿ` 乗。 -/
noncomputable def perfectionRootStageEquiv [IsReduced D] (n : ℕ) :
    D ≃+* perfectionRootStage D p n :=
  RingEquiv.ofBijective (perfectionRootHom D p n).rangeRestrict
    ⟨fun _ _ heq ↦ perfectionRootHom_injective D p n (congrArg Subtype.val heq),
      RingHom.rangeRestrict_surjective _⟩

/-- 根の段の環同型を perfection に入れると、根の写像になる。 -/
@[simp] theorem perfectionRootStageEquiv_coe [IsReduced D] (n : ℕ) (x : D) :
    (perfectionRootStageEquiv D p n x : PerfectClosure D p) = perfectionRootHom D p n x := by rfl

/-- 整拡大の perfection も、構造写像が両立する基底環上整である。
各元の `pⁿ` 乗を元の環へ戻し、整性が冪から元へ降りる Mathlib の定理を使う。 -/
theorem isIntegral_perfection_of_isIntegral
    (R : Type u) [CommRing R] [Algebra R D] [Algebra.IsIntegral R D]
    [Algebra R (PerfectClosure D p)]
    (hbase : ∀ r : R, algebraMap R (PerfectClosure D p) r =
      PerfectClosure.of D p (algebraMap R D r)) (x : PerfectClosure D p) :
    IsIntegral R x := by
  let f : D →ₐ[R] PerfectClosure D p :=
    { PerfectClosure.of D p with commutes' := fun r ↦ (hbase r).symm }
  induction x using PerfectClosure.induction_on with
  | h x =>
      apply IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos x.1)
      rw [perfection_mk_pow]
      exact (Algebra.IsIntegral.isIntegral x.2).map f

/-- 根の段への通常の包含。根を取る環同型とは異なり、元を元のまま埋め込む。 -/
noncomputable def perfectionRootStageBaseMap [IsReduced D] (n : ℕ) :
    D →+* perfectionRootStage D p n :=
  (perfectionRootStageEquiv D p n).toRingHom.comp (iterateFrobenius D p n)

/-- 元の `pⁿ` 乗の根は、通常の包含で送った元に等しい。 -/
@[simp] theorem perfectionRootStageEquiv_pow [IsReduced D] (n : ℕ) (x : D) :
    perfectionRootStageEquiv D p n (x ^ (p ^ n)) = perfectionRootStageBaseMap D p n x := by
  rfl

/-- 通常の包含を perfection まで合成すると、標準写像になる。 -/
theorem perfectionRootStageBaseMap_coe [IsReduced D] (n : ℕ) (x : D) :
    (perfectionRootStageBaseMap D p n x : PerfectClosure D p) = PerfectClosure.of D p x := by
  change perfectionRootHom D p n (x ^ (p ^ n)) = _
  rw [map_pow, perfectionRootHom_apply, perfection_mk_pow]

variable (R : Type u) [CommRing R] [Algebra R (PerfectClosure D p)]

/-- `R` と `D^{1/pⁿ}` が生成する部分代数。定理2.5では `R = Λ` とする。 -/
@[expose] noncomputable def perfectionApproximation (n : ℕ) : Subalgebra R (PerfectClosure D p) :=
  Algebra.adjoin R (Set.range (perfectionRootHom D p n))

/-- 次の段の `p` 乗から現在の段が得られるので、部分代数は増大する。 -/
theorem perfectionApproximation_monotone : Monotone (perfectionApproximation D p R) := by
  apply monotone_nat_of_le_succ
  intro n
  apply Algebra.adjoin_le
  rintro _ ⟨x, rfl⟩
  have hx : perfectionRootHom D p (n + 1) x ∈ perfectionApproximation D p R (n + 1) :=
    Algebra.subset_adjoin (Set.mem_range_self x)
  have heq : perfectionRootHom D p n x = perfectionRootHom D p (n + 1) x ^ p := by
    rw [perfectionRootHom_apply, perfectionRootHom_apply, PerfectClosure.mk_pow,
      PerfectClosure.mk_succ_pow]
  rw [heq]
  exact (perfectionApproximation D p R (n + 1)).pow_mem hx p

/-- Perfection の各元はある段の部分代数に属する。 -/
theorem exists_mem_perfectionApproximation (x : PerfectClosure D p) :
    ∃ n, x ∈ perfectionApproximation D p R n := by
  induction x using PerfectClosure.induction_on with
  | h x =>
      refine ⟨x.1, ?_⟩
      rw [← perfectionRootHom_apply]
      exact Algebra.subset_adjoin (Set.mem_range_self x.2)

/-- 固定した商 `C/J` の中で、第 `n` 段の近似部分代数から来る元の部分加群。
商写像の像を同じ加群の中で比較するための数学的な対象である。 -/
@[expose] noncomputable def perfectionQuotientImage (J : Ideal (PerfectClosure D p)) (n : ℕ) :
    Submodule R ((PerfectClosure D p) ⧸ J) :=
  (perfectionApproximation D p R n).toSubmodule.map (J.mkQ.restrictScalars R)

/-- 近似環が増大するので、固定した商の中の像も増大する。 -/
theorem perfectionQuotientImage_monotone (J : Ideal (PerfectClosure D p)) :
    Monotone (perfectionQuotientImage D p R J) := by
  intro n m hnm
  exact Submodule.map_mono (perfectionApproximation_monotone D p R hnm)

/-- 近似環が perfection を覆うので、その商の中の像も商全体を覆う。 -/
theorem iSup_perfectionQuotientImage (J : Ideal (PerfectClosure D p)) :
    (⨆ n, perfectionQuotientImage D p R J n) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := exists_mem_perfectionApproximation D p R c
  exact (le_iSup (perfectionQuotientImage D p R J) n)
    (Submodule.mem_map.mpr ⟨c, hn, rfl⟩)

/-- 有限段の近似に対する、共通分母からの核の評価。
長さの有限性と共通分母の条件を明示的に受け取る。この二条件を定理2.5の設定で
得るためには、それぞれテンソル積表示とトレースの議論が別途必要である。 -/
theorem perfectionApproximation_kernel_bound {J : Ideal R} (lam : NormalizedLength R J)
    (n : ℕ) (I : Ideal (perfectionApproximation D p R n))
    (g : perfectionApproximation D p R n)
    (hg : ∀ c : PerfectClosure D p, (g : PerfectClosure D p) * c ∈
      perfectionApproximation D p R n)
    (htors : IsPowTorsion J ((perfectionApproximation D p R n) ⧸ I))
    (hfinite : lam.len ((perfectionApproximation D p R n) ⧸ I) ≠ ⊤) :
    lam.len (LinearMap.ker
      ((quotientToExtension (C := PerfectClosure D p) I).toLinearMap.restrictScalars R)) ≤
    lam.len ((perfectionApproximation D p R n) ⧸ (I ⊔ Ideal.span {g})) := by
  apply len_ker_quotientToExtension_le R lam Subtype.val_injective I g _ htors hfinite
  intro c
  exact ⟨⟨(g : PerfectClosure D p) * c, hg c⟩, rfl⟩

/-- Perfection の分数体は、元の環を含む底体上純非分離である。
各元を根の段に表示して、その `pⁿ` 乗を底環に戻す。
分数体の元については、既存の分子・分母の冪をそろえる一般論を使う。 -/
theorem perfectClosure_fractionRing_isPurelyInseparable
    (K L : Type u) [Field K] [Field L] [ExpChar K p]
    [Algebra D (PerfectClosure D p)] [Algebra D K] [Algebra D L]
    [Algebra (PerfectClosure D p) L] [IsFractionRing (PerfectClosure D p) L]
    [Algebra K L] [IsScalarTower D K L] [IsScalarTower D (PerfectClosure D p) L]
    (hbase : ∀ d : D, algebraMap D (PerfectClosure D p) d = PerfectClosure.of D p d) :
    IsPurelyInseparable K L := by
  apply isPurelyInseparable_fractionRing_of_pow_mem (PerfectClosure D p) K L p
  intro c
  induction c using PerfectClosure.induction_on with
  | h c =>
      refine ⟨c.1, algebraMap D K c.2, ?_⟩
      rw [← IsScalarTower.algebraMap_apply D K L,
        IsScalarTower.algebraMap_apply D (PerfectClosure D p) L, hbase,
        ← map_pow, perfection_mk_pow]

attribute [local instance] FractionRing.liftAlgebra

/-- 正規整域の perfection は正規である。
perfection の整性と分数体拡大の純非分離性を証明し、完全な整拡大の一般論を使う。
元の環の正規性以外に、Noether 性や正則性は要求しない。 -/
theorem perfectClosure_isIntegrallyClosed [IsDomain D] [IsIntegrallyClosed D] :
    IsIntegrallyClosed (PerfectClosure D p) := by
  let C := PerfectClosure D p
  let := perfectClosure_isDomain D p
  let : Algebra D C := (PerfectClosure.of D p).toAlgebra
  let : FaithfulSMul D C := (faithfulSMul_iff_algebraMap_injective D C).mpr (by
    intro x y hxy
    apply perfectionRootHom_injective D p 0
    change PerfectClosure.of D p x = PerfectClosure.of D p y at hxy
    simpa only [perfectionRootHom_apply, PerfectClosure.of_apply] using hxy)
  let : Algebra.IsIntegral D C := ⟨fun x ↦ isIntegral_perfection_of_isIntegral D p D
    (fun _ ↦ rfl) x⟩
  let K := FractionRing D
  let L := FractionRing C
  let : IsPurelyInseparable K L :=
    perfectClosure_fractionRing_isPurelyInseparable D p K L (fun _ ↦ rfl)
  exact isIntegrallyClosed_of_perfect_of_purelyInseparable D C K L p

end SerrePositivity.Section2
