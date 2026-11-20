module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformPivotElimination

/-!
概要：KST §5、Stacks 0810・080Z の正則な境界の下での純変換の実同型。
方針：境界の冪で消える核を擬関係式の像へ移し、可逆な成分で消去する。
規約：元の加群と既存の純変換を使い、別の自由加群を純変換として定義しない。
使われ方：正則な小行列式による生成元削減を自由性へ強める。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R P Q M : Type*} [CommRing R] [AddCommGroup P] [AddCommGroup Q]
  [AddCommGroup M] [Module R P] [Module R Q] [Module R M]

/--
概要：正則な境界と可逆な第一成分を持つ擬関係式の下で残りの成分は純変換へ単射に写る。
方針：純変換の核の元の境界冪倍を元の核へ移し、第一成分を用いて擬関係式を消す。
規約：KST §5、Stacks 0810, Lemma 38.30.2・080Z, Lemma 15.8.9、核の包含を明示する。
使われ方：実際の純変換と残りの自由生成元との線形同型の構成。
-/
theorem pureTransformPivotComplement_injective (f : R)
    (q : (P × Q) →ₗ[R] M) (t : P →ₗ[R] (P × Q)) (e : P ≃ₗ[R] P)
    (hf : IsSMulRegular Q f) (hker : LinearMap.ker q ≤ LinearMap.range t)
    (hfst : (LinearMap.fst R P Q).comp t = e.toLinearMap) :
    Function.Injective (((boundaryTorsion f M).mkQ.comp q).comp (LinearMap.inr R P Q)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hyq : q (0, y) ∈ boundaryTorsion f M :=
    (Submodule.Quotient.mk_eq_zero _).mp hy
  obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff f M (q (0, y))).mp hyq
  have hyker : (0, f ^ n • y) ∈ LinearMap.ker q := by
    change q (0, f ^ n • y) = 0
    simpa only [← map_smul, Prod.smul_mk, smul_zero] using hn
  obtain ⟨x, hx⟩ := hker hyker
  have hx0 : x = 0 := by
    have hex : e x = 0 :=
      (LinearMap.congr_fun hfst x).symm.trans (congrArg Prod.fst hx)
    exact e.injective (hex.trans e.map_zero.symm)
  have hys : f ^ n • y = 0 := by
    have h := congrArg Prod.snd hx
    simpa only [hx0, map_zero, Prod.snd_zero] using h.symm
  exact (hf.pow n) (by simpa only [smul_zero] using hys)

/--
概要：正則な境界と完全性を持つ擬関係式の下で残りの成分と純変換は実際に線形同型。
方針：既存の生成元消去の全射性と境界の正則性による単射性を組み合わせる。
規約：KST §5、Stacks 0810・080Z、純変換を既存の境界ねじれの商として保持する。
使われ方：正則単項小行列式による純変換の局所自由性。
-/
def pureTransformPivotComplementEquiv (f : R)
    (q : (P × Q) →ₗ[R] M) (t : P →ₗ[R] (P × Q)) (e : P ≃ₗ[R] P)
    (hf : IsSMulRegular Q f) (hq : Function.Surjective q)
    (ht : ∀ x, q (t x) ∈ boundaryTorsion f M)
    (hker : LinearMap.ker q ≤ LinearMap.range t)
    (hfst : (LinearMap.fst R P Q).comp t = e.toLinearMap) :
    Q ≃ₗ[R] modulePureTransform f M :=
  LinearEquiv.ofBijective (((boundaryTorsion f M).mkQ.comp q).comp (LinearMap.inr R P Q))
    ⟨pureTransformPivotComplement_injective f q t e hf hker hfst,
      pureTransformPivotComplement_surjective f q t e hq ht hfst⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
