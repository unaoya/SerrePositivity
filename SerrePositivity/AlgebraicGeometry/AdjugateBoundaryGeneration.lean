module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.AdjugateRelationElimination
public import SerrePositivity.AlgebraicGeometry.PureTransformBoundaryComparison
public import SerrePositivity.AlgebraicGeometry.LocalMinorPureTransformGeneration

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の小行列式の共通因子から元の境界の純変換への生成。
方針：共通因子による生成元削減を、異なる境界元の純変換の実全射で移す。
規約：共通因子 c が境界元 f の一つの冪を割ることを明示する。
使われ方：係数 blowup の局所環で strict transform の元の境界に沿う生成元数を評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：小行列式の共通因子が境界冪を割れば、元の境界の純変換も残りの生成元からの実全射を持つ。
方針：随伴行列による共通因子に沿う全射と、元の境界に沿う純変換への比較全射を合成する。
規約：KST §5、Stacks 0810, Lemma 38.30.2 と 080Z, Lemma 15.8.9、二つの元を区別する。
使われ方：strict transform の生成元数を共通因子の小行列式条件から導く。
-/
theorem adjugate_boundary_complement_surjective
    {R M ι κ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι]
    (c f : R) (N : ℕ) (hcf : c ∣ f ^ N) (u : Rˣ)
    (A : Matrix ι ι R) (B : Matrix κ ι R)
    (q : ((ι → R) × (κ → R)) →ₗ[R] M) (hq : Function.Surjective q)
    (hrel : q.comp (A.mulVecLin.prod B.mulVecLin) = 0)
    (hdet : A.det = c * (u : R))
    (hdiv : ∀ i j, c ∣ (A.updateRow j (B i)).det) :
    Function.Surjective (((boundaryTorsion f M).mkQ.comp q).comp
      (LinearMap.inr R (ι → R) (κ → R))) := by
  have h := adjugate_pureTransform_complement_surjective_of_minors_dvd c u A B q hq hrel hdet hdiv
  exact (modulePureTransformBoundaryMap_surjective c f M N hcf).comp h

/--
概要：正則単項の小行列式と境界冪への可除性から、元の境界の純変換の有限生成元数を削減する。
方針：共通因子の純変換の有限自由加群からの全射を作り、境界比較の全射と合成する。
規約：KST §5、Stacks 0810, Lemma 38.30.2 と 080Z, Lemma 15.8.9、局所環での正則単項特殊形。
使われ方：係数 blowup の特別な局所環で元の境界に沿う純変換の生成元数を得る。
-/
theorem exists_fin_surjection_boundaryPureTransform_of_regular_minorIdeal
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Fintype m] (H : Matrix m n R) (k : ℕ) (c f : R) (hc : IsRegular c)
    (N : ℕ) (hcf : c ∣ f ^ N) (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hrel : ∀ j, q (H.col j) = 0) (hI : matrixMinorIdeal H k = Ideal.span {c}) :
    ∃ g : (Fin (Fintype.card m - k) → R) →ₗ[R] modulePureTransform f M,
      Function.Surjective g := by
  obtain ⟨g, hg⟩ := exists_fin_surjection_pureTransform_of_regular_minorIdeal H k c hc q hq hrel hI
  exact ⟨(modulePureTransformBoundaryMap c f M N hcf).comp g,
    (modulePureTransformBoundaryMap_surjective c f M N hcf).comp hg⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
