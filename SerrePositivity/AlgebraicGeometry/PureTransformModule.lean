module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Module.FinitePresentation

/-!
概要：Stacks 0815, Theorem 38.30.7 の Cartier 境界に沿う加群の純変換の基礎。
方針：一元局所化写像の核を境界ねじれとし、その商を使う。
規約：境界元は基礎環の像としても使用でき、ここでは任意の可換環の元を扱う。
使われ方：KST §5、Stacks 081T に必要な Noether 特殊形の平坦化の準備。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (f : R) (M : Type*) [AddCommGroup M] [Module R M]

/--
概要：境界元の冪で消える元の部分加群。
方針：境界元による局所化写像の核を取る。
規約：Stacks 0815、境界元の正則性は定義には仮定しない。
使われ方：純変換で除く境界支持のねじれ。
-/
def boundaryTorsion : Submodule R M :=
  LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers f) M)

/--
概要：境界支持のねじれを除いた加群の純変換。
方針：局所化写像の核で商を取る。
規約：Stacks 0815、スキームの strict transform とは別の加群の構成。
使われ方：blowup チャート上の基底変更加群に適用する。
-/
abbrev modulePureTransform := M ⧸ boundaryTorsion f M

/--
概要：境界ねじれへの所属は一つの冪による消滅と同値。
方針：局所化写像の核の既存の判定を使う。
規約：Stacks 0815、冪の指数は元に依存する。
使われ方：分母消去と純変換の正則性。
-/
theorem mem_boundaryTorsion_iff (m : M) :
    m ∈ boundaryTorsion f M ↔ ∃ n : ℕ, f ^ n • m = 0 := by
  rw [boundaryTorsion, LocalizedModule.mem_ker_mkLinearMap_iff]
  constructor
  · rintro ⟨r, ⟨n, rfl⟩, h⟩
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨f ^ n, ⟨n, rfl⟩, h⟩

/--
概要：境界元を掛けた元が境界ねじれなら元自身も境界ねじれ。
方針：消滅指数を一つ増やす。
規約：Stacks 0815、環と加群に Noether 条件を課さない。
使われ方：純変換での境界元の正則性。
-/
theorem smul_mem_boundaryTorsion_iff (m : M) :
    f • m ∈ boundaryTorsion f M ↔ m ∈ boundaryTorsion f M := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff f M _).mp h
    apply (mem_boundaryTorsion_iff f M _).mpr
    exact ⟨n + 1, by simpa [pow_succ, mul_smul] using hn⟩
  · exact (boundaryTorsion f M).smul_mem f

/--
概要：純変換上で境界元の作用は単射。
方針：商の等式を差のねじれ所属に移して飽和性を使う。
規約：Stacks 0815、元の加群の平坦性は不要。
使われ方：境界ねじれを除いたことの検証。
-/
theorem modulePureTransform_isSMulRegular : IsSMulRegular (modulePureTransform f M) f := by
  intro x y h
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) y
  apply (Submodule.Quotient.eq _).mpr
  apply (smul_mem_boundaryTorsion_iff f M _).mp
  rw [smul_sub]
  exact (Submodule.Quotient.eq _).mp h

/--
概要：境界元が正則に作用する加群には境界ねじれがない。
方針：正則性を冪へ移し、消滅判定に適用する。
規約：Stacks 0815、正則性は加群上の作用について仮定する。
使われ方：平坦な加群の純変換の同定。
-/
theorem boundaryTorsion_eq_bot_of_isSMulRegular (hf : IsSMulRegular M f) :
    boundaryTorsion f M = ⊥ := by
  apply eq_bot_iff.mpr
  intro m hm
  obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff f M m).mp hm
  exact (hf.pow n) (by simpa using hn)

/--
概要：正則な境界元と平坦な加群では境界ねじれは零。
方針：平坦性による正則性の保存を使う。
規約：Stacks 0815、境界元は環上で正則とする。
使われ方：既に平坦な開部分で純変換が元の加群と一致すること。
-/
theorem boundaryTorsion_eq_bot_of_flat [Module.Flat R M] (hf : IsRegular f) :
    boundaryTorsion f M = ⊥ :=
  boundaryTorsion_eq_bot_of_isSMulRegular f M (Module.Flat.isSMulRegular_of_isRegular hf)

/--
概要：純変換と局所化写像の像の実際の線形同型。
方針：線形写像の第一同型定理を使う。
規約：Stacks 0815、局所化全体ではなく元の加群の像と同定する。
使われ方：純変換から局所化への単射と局所化後の比較。
-/
def modulePureTransformEquivRange : modulePureTransform f M ≃ₗ[R]
    LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M) :=
  (LocalizedModule.mkLinearMap (Submonoid.powers f) M).quotKerEquivRange

/--
概要：有限加群の純変換は有限加群。
方針：有限加群の商の有限性を使う。
規約：Stacks 0815、基礎環の Noether 条件は不要。
使われ方：Noether チャート上の有限表示性への入力。
-/
theorem modulePureTransform_finite [Module.Finite R M] :
    Module.Finite R (modulePureTransform f M) := inferInstance

/--
概要：有限生成の境界ねじれは一つの境界元の冪で全体が消える。
方針：有限生成元の消滅指数の最大値を取り、生成する部分加群へ広げる。
規約：Stacks 0815、有限生成性はねじれ部分加群だけに仮定する。
使われ方：Noether チャート上の一様な分母消去。
-/
theorem exists_pow_annihilates_boundaryTorsion
    (hfg : (boundaryTorsion f M).FG) :
    ∃ n : ℕ, ∀ m ∈ boundaryTorsion f M, f ^ n • m = 0 := by
  classical
  obtain ⟨s, hs⟩ := hfg
  have hgen : ∀ m ∈ s, ∃ n : ℕ, f ^ n • m = 0 := by
    intro m hm
    apply (mem_boundaryTorsion_iff f M m).mp
    rw [← hs]
    exact Submodule.subset_span hm
  choose n hn using hgen
  let N := s.attach.sup (fun m => n m.val m.property)
  refine ⟨N, ?_⟩
  have hle : Submodule.span R (s : Set M) ≤ Submodule.torsionBy R M (f ^ N) := by
    apply Submodule.span_le.mpr
    intro m hm
    apply (Submodule.mem_torsionBy_iff _ _).mpr
    have hnm : n m hm ≤ N := Finset.le_sup (f := fun m => n m.val m.property)
      (Finset.mem_attach s ⟨m, hm⟩)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm
    rw [hk, pow_add, mul_smul, smul_comm, hn m hm, smul_zero]
  intro m hm
  exact (Submodule.mem_torsionBy_iff _ _).mp (hle (by rwa [hs]))

/--
概要：Noether 環上の有限加群の境界ねじれを一様な冪が消す。
方針：ねじれ部分加群の有限生成性を Noether 性から得る。
規約：Stacks 0815、有限性はこの環上の加群について仮定する。
使われ方：有限型代数を環として使うチャートでの分母消去。
-/
theorem exists_pow_annihilates_boundaryTorsion_of_noetherian
    [IsNoetherianRing R] [Module.Finite R M] :
    ∃ n : ℕ, ∀ m ∈ boundaryTorsion f M, f ^ n • m = 0 :=
  exists_pow_annihilates_boundaryTorsion f M (IsNoetherian.noetherian _)

/--
概要：Noether 環上の有限加群の純変換は有限表示。
方針：商の有限性と Noether 環上の有限表示判定を使う。
規約：Stacks 0815、これだけから基礎環上の平坦性は推論しない。
使われ方：純変換の平坦化の有限表示条件。
-/
theorem modulePureTransform_finitePresentation
    [IsNoetherianRing R] [Module.Finite R M] :
    Module.FinitePresentation R (modulePureTransform f M) :=
  Module.finitePresentation_of_finite R _

variable {M} {N : Type*} [AddCommGroup N] [Module R N]

/--
概要：線形写像は境界ねじれを境界ねじれへ送る。
方針：一つの冪による消滅を写像で送る。
規約：Stacks 0815、同じ境界元を両加群で使う。
使われ方：加群の純変換の関手性。
-/
theorem boundaryTorsion_map_le (g : M →ₗ[R] N) :
    boundaryTorsion f M ≤ (boundaryTorsion f N).comap g := by
  intro m hm
  obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff f M m).mp hm
  exact (mem_boundaryTorsion_iff f N (g m)).mpr
    ⟨n, by rw [← g.map_smul, hn, g.map_zero]⟩

/--
概要：線形写像による純変換の間の実際の写像。
方針：境界ねじれを保つ写像を商へ降ろす。
規約：Stacks 0815、写像は元の環上線形。
使われ方：平坦化で使う加群の表示の比較。
-/
def modulePureTransformMap (g : M →ₗ[R] N) :
    modulePureTransform f M →ₗ[R] modulePureTransform f N :=
  (boundaryTorsion f M).mapQ (boundaryTorsion f N) g (boundaryTorsion_map_le f g)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
