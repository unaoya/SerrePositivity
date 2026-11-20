module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の可逆な関係式による生成元の除去。
方針：関係式の可逆な成分を使って、生成元の直和の一方の成分を消す。
規約：任意の加群で明示的な線形写像を使い、有限性や局所環の条件は仮定しない。
使われ方：単元小行列式による生成元数と自由性の判定。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R P Q M : Type*} [CommRing R] [AddCommGroup P] [AddCommGroup Q]
  [AddCommGroup M] [Module R P] [Module R Q] [Module R M]

/--
概要：関係式の一成分が可逆なら残りの成分からの写像は全射。
方針：任意の原像から関係式の適切な元を引き、最初の成分を零にする。
規約：KST §5、Stacks 0810, Lemma 38.30.2、q は元の生成元からの全射。
使われ方：単元小行列式に対応する生成元を除去する。
-/
theorem relationPivotComplement_surjective
    (q : (P × Q) →ₗ[R] M) (t : P →ₗ[R] (P × Q)) (e : P ≃ₗ[R] P)
    (hq : Function.Surjective q) (hqt : q.comp t = 0)
    (hfst : (LinearMap.fst R P Q).comp t = e.toLinearMap) :
    Function.Surjective (q.comp (LinearMap.inr R P Q)) := by
  intro m
  obtain ⟨z, rfl⟩ := hq m
  have ht : ∀ x, (t x).1 = e x := fun x => LinearMap.congr_fun hfst x
  have hzero : ∀ x, q (t x) = 0 := fun x => LinearMap.congr_fun hqt x
  have hz : z - t (e.symm z.1) = (0, z.2 - (t (e.symm z.1)).2) := by
    apply Prod.ext
    · simp only [Prod.fst_sub, ht, e.apply_symm_apply, sub_self]
    · rfl
  refine ⟨z.2 - (t (e.symm z.1)).2, ?_⟩
  change q (0, z.2 - (t (e.symm z.1)).2) = q z
  rw [← hz, map_sub, hzero, sub_zero]

/--
概要：関係式が核全体を与え可逆な成分を持てば、残りの成分からの写像は単射。
方針：核の元を関係式の像として表し、その最初の成分の単射性を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、核と像の等式を明示する。
使われ方：生成元の除去後に残る自由加群との同型。
-/
theorem relationPivotComplement_injective
    (q : (P × Q) →ₗ[R] M) (t : P →ₗ[R] (P × Q)) (e : P ≃ₗ[R] P)
    (hker : LinearMap.ker q = LinearMap.range t)
    (hfst : (LinearMap.fst R P Q).comp t = e.toLinearMap) :
    Function.Injective (q.comp (LinearMap.inr R P Q)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hyker : (0, y) ∈ LinearMap.ker q := hy
  rw [hker] at hyker
  obtain ⟨x, hx⟩ := hyker
  have hx0 : x = 0 := by
    have hex : e x = 0 := (LinearMap.congr_fun hfst x).symm.trans (congrArg Prod.fst hx)
    exact e.injective (hex.trans e.map_zero.symm)
  have h := congrArg Prod.snd hx
  simpa only [hx0, map_zero, Prod.snd_zero] using h.symm

/--
概要：可逆な成分を持つ完全な関係式の下で、残りの加群と対象の実際の線形同型。
方針：残りの成分からの写像の全単射性を使って同型を構成する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の対象 M を別の商で再定義しない。
使われ方：表示行列の可逆小行列を消去した後の自由性。
-/
def relationPivotComplementEquiv
    (q : (P × Q) →ₗ[R] M) (t : P →ₗ[R] (P × Q)) (e : P ≃ₗ[R] P)
    (hq : Function.Surjective q) (hqt : q.comp t = 0)
    (hker : LinearMap.ker q = LinearMap.range t)
    (hfst : (LinearMap.fst R P Q).comp t = e.toLinearMap) : Q ≃ₗ[R] M :=
  LinearEquiv.ofBijective (q.comp (LinearMap.inr R P Q))
    ⟨relationPivotComplement_injective q t e hker hfst,
      relationPivotComplement_surjective q t e hq hqt hfst⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
