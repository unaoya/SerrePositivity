module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.Exceptional

/-!
概要：KST §5 の例外因子の有効 Cartier 性をアフィン局所モデルで表す。
方針：実際の閉埋め込みの逆像を非零因子で定義された商の Spec に同定する。
規約：Stacks 01WQ, Lemma 31.14.2 のアフィン局所的な特徴付けを定義に採る。
使われ方：blowup の例外因子と Stacks 081T の Cartier 化の入力。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

/--
概要：閉埋め込みが局所的に非零因子一つで切り出されるという有効 Cartier 条件。
方針：各点のアフィン開近傍上で、実際の逆像と商の Spec の包含を保つ同型を要求する。
規約：KST §5、Stacks 01WQ Lemma 31.14.2 の局所モデル。中心外の点も被覆する。
使われ方：Mathlib に未定義の有効 Cartier 性を、既存の Scheme と環の言葉で表す。
-/
def IsEffectiveCartierImmersion {D X : Scheme.{u}} (i : D ⟶ X) : Prop :=
  IsClosedImmersion i ∧ ∀ x : X,
    ∃ (A : CommRingCat.{u}) (j : Spec A ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j ∧
      ∃ (J : Ideal A) (r : A), r ∈ nonZeroDivisors A ∧ J = Ideal.span {r} ∧
        ∃ e : pullback i j ≅ Spec (.of (A ⧸ J)),
          e.inv ≫ pullback.snd i j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

variable {R : Type u} [CommRing R] (I : Ideal R)

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン blowup の例外閉部分スキームは有効 Cartier 因子。
方針：標準チャート被覆、商の Spec への同型、中心の単項生成と非零因子性を組み合わせる。
規約：KST §5、Stacks 01WQ Lemma 31.14.2。Noether 性や中心の有限生成性は不要。
使われ方：例外因子の局所正則方程式を Stacks 081T と通常 blowup の比較に渡す。
-/
theorem affineExceptional_isEffectiveCartier :
    IsEffectiveCartierImmersion (affineExceptionalι I) := by
  refine ⟨inferInstance, ?_⟩
  intro x
  have htop : x ∈ (⊤ : (affineBlowup I).Opens) := trivial
  rw [← iSup_affineBlowupChart I] at htop
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  refine ⟨CommRingCat.of (BlowupChartRing I a), affineBlowupChartι I a, inferInstance, ?_,
    I.map (chartBaseMap I a), chartBaseMap I a a.1, chartBaseMap_mem_nonZeroDivisors I a,
    chart_map_ideal_eq_span I a, affineExceptionalChartIso I a,
    affineExceptionalChartIso_inv_snd I a⟩
  change x ∈ (affineBlowupChartι I a).opensRange
  rw [show (affineBlowupChartι I a).opensRange = affineBlowupChart I a from
    Proj.opensRange_awayι ..]
  exact ha

/--
概要：非零因子で生成される単項イデアルは階数一の自由加群。
方針：生成元による乗法が全単射であることを示す。
規約：KST §5、Stacks 01WQ Lemma 31.14.2 の可逆イデアルの局所環論。
使われ方：例外イデアルの局所自明化を実際の線形同型として得る。
-/
def regularPrincipalIdealEquiv {A : Type*} [CommRing A] (r : A)
    (hr : r ∈ nonZeroDivisors A) : A ≃ₗ[A] Ideal.span {r} :=
  LinearEquiv.ofBijective
    { toFun := fun z => ⟨z * r, Ideal.mem_span_singleton'.mpr ⟨z, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (add_mul x y r)
      map_smul' := fun c z => Subtype.ext (mul_assoc c z r) }
    ⟨fun x y h => by
      have hmul : (x - y) * r = 0 := by
        rw [sub_mul, sub_eq_zero]
        exact congrArg Subtype.val h
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hr) _ hmul),
      fun z => by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp z.2
        exact ⟨c, Subtype.ext hc⟩⟩

/--
概要：標準 blowup チャート上の中心の拡大イデアルを係数環と線形同型にする。
方針：a の非零因子性と拡大イデアルの単項生成を使う。
規約：KST §5、例外イデアルの生成元は基礎環の a の像。
使われ方：例外因子の可逆イデアルの各チャート上の自明化。
-/
def chartExceptionalIdealEquiv (a : I) :
    BlowupChartRing I a ≃ₗ[BlowupChartRing I a] I.map (chartBaseMap I a) :=
  regularPrincipalIdealEquiv (chartBaseMap I a a.1)
      (chartBaseMap_mem_nonZeroDivisors I a) ≪≫ₗ
    LinearEquiv.ofEq _ _ (chart_map_ideal_eq_span I a).symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
