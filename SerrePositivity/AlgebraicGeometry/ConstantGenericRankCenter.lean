module

public import SerrePositivity.AlgebraicGeometry.BoundaryMinorCoefficientPower
public import SerrePositivity.AlgebraicGeometry.CoefficientBlowupGenericFree
public import SerrePositivity.AlgebraicGeometry.FinitePresentationMatrix

/-!
概要：KST §5、Stacks 0810 の一定の境界外一般階数に対する実際の係数中心。
方針：境界冪の所属と高次小行列式の消滅から、中心の有限生成性・補開集合・チャートの自由性をまとめる。
規約：元の有限表示と代数の実分裂を固定する。
使われ方：有限型加群の平坦化で一般点を自由化する段階の具体的な中心。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：境界外の平坦性と一定一般階数から、全チャートの拡大素点で純変換を自由にする有限生成中心を得る。
方針：係数中心を具体的に定義し、境界冪の所属・小行列式の消滅・実チャートの自由性を接続する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、階数は生成元数とピボット次数の差で述べる。
使われ方：一般有限型加群の平坦化で純変換の自由 locus を作る準備。
-/
theorem constant_boundary_generic_rank_coefficient_center
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι m n : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q) (H : Matrix m n B)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] (r : ℕ)
    (hrank :
      let F := Localization.Away f
      let D := F ⊗[A] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
        geometricallyIntegral_tensorProjection A B F
      ∀ P : PrimeSpectrum F,
        let L := Localization.AtPrime (geometricallyIntegralGenericPrime F D P).asIdeal
        Module.finrank L (L ⊗[D] (D ⊗[B] M)) = r) :
    let k := Fintype.card m - r
    let J := boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k))
    J.FG ∧ affineCenterComplement J = PrimeSpectrum.basicOpen f ∧
      ∀ a : J,
        let C := BlowupChartRing J a
        letI : Algebra A C := (chartBaseMap J a).toAlgebra
        letI : IsNoetherianRing C := blowupChartRing_isNoetherianRing J a
        GenericBoundaryPureFree A B C M (chartBaseMap J a f) (Fintype.card m - k) := by
  classical
  let k := Fintype.card m - r
  let J := boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k))
  obtain ⟨N, hn⟩ := exists_pow_mem_minorCoefficient_of_boundary_genericRank A B e p hpe
    q hq H hH f r hrank
  have hzero : matrixMinorIdeal H (k + 1) = ⊥ :=
    higherMinorIdeal_eq_bot_of_boundary_genericRank A B e p hpe q hq H hH f hf r hrank
      (k + 1) (Nat.lt_succ_self k)
  have hfg : J.FG := boundaryMultipleCenter_fg f _
    (splitAlgebraCoefficientIdeal_fg e p hpe _ (matrixMinorIdeal_fg H k))
  refine ⟨hfg, ?_, ?_⟩
  · exact boundaryMultipleCenter_complement f _ N hn
  · intro a
    exact coefficientBlowup_chart_boundary_free_and_finrank A B e p hpe H k q hq hH
      hzero f hf N hn a

/--
概要：境界外で平坦で一定一般階数を持つ有限加群には全チャートの一般点で純変換を自由にする中心が存在する。
方針：Noether 性から実際の完全な有限表示を選び、具体的な係数中心の定理へ渡す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、表示を未証明の仮定として要求しない。
使われ方：実分裂の下での一般点自由化中心の存在を開自由 locus へ接続する。
-/
theorem exists_fg_center_genericBoundaryPureFree_of_constant_boundary_rank
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] (r : ℕ)
    (hrank :
      let F := Localization.Away f
      let D := F ⊗[A] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
        geometricallyIntegral_tensorProjection A B F
      ∀ P : PrimeSpectrum F,
        let L := Localization.AtPrime (geometricallyIntegralGenericPrime F D P).asIdeal
        Module.finrank L (L ⊗[D] (D ⊗[B] M)) = r) :
    ∃ (J : Ideal A) (s : ℕ),
      J.FG ∧ affineCenterComplement J = PrimeSpectrum.basicOpen f ∧
        ∀ a : J,
          let C := BlowupChartRing J a
          letI : Algebra A C := (chartBaseMap J a).toAlgebra
          letI : IsNoetherianRing C := blowupChartRing_isNoetherianRing J a
          GenericBoundaryPureFree A B C M (chartBaseMap J a f) s := by
  classical
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
  obtain ⟨N, t, q, H, hq, hH⟩ := exists_finite_presentation_matrix B M
  let k := Fintype.card (Fin N) - r
  let J := boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k))
  refine ⟨J, Fintype.card (Fin N) - k, ?_⟩
  exact constant_boundary_generic_rank_coefficient_center A B e p hpe q hq H hH f hf r hrank

end SerrePositivity.AlgebraicGeometry


/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
