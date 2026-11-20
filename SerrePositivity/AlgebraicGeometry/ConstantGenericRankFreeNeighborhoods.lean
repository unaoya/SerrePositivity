module

public import SerrePositivity.AlgebraicGeometry.ConstantGenericRankCenter
public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoods

/-!
概要：KST §5、Stacks 0810 の一定の境界外一般階数に対する自由な基本開近傍を持つ中心。
方針：表示行列から実際に構成した有限生成中心を各チャートの自由化元の存在へ接続する。
規約：実分裂と境界外の一定一般階数を入力し、K 理論には依存しない。
使われ方：一般有限型加群の平坦化で一般点を含む自由な開部分を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：境界外で平坦かつ一定一般階数の有限加群に、全チャートで自由な基本開近傍を持つ有限生成中心が存在する。
方針：実際の有限表示から係数中心を選び、各チャートの拡大素点の自由性を基本開へ降ろす。
規約：KST §5、Stacks 0810, Lemma 38.30.2 の Noether・実分裂の特殊形。
使われ方：純変換の自由な開部分で基礎環を覆い、平坦化の帰納法へ渡す。
-/
theorem exists_fg_center_freeNeighborhoods_of_constant_boundary_rank
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
          BoundaryPureFreeNeighborhoods A B C M (chartBaseMap J a f) s := by
  obtain ⟨J, s, hfg, hJ, hGF⟩ :=
    exists_fg_center_genericBoundaryPureFree_of_constant_boundary_rank A B e p hpe f hf r hrank
  refine ⟨J, s, hfg, hJ, ?_⟩
  intro a
  let C := BlowupChartRing J a
  let : Algebra A C := (chartBaseMap J a).toAlgebra
  let : IsNoetherianRing C := blowupChartRing_isNoetherianRing J a
  exact boundaryPureFreeNeighborhoods_of_genericBoundaryPureFree A B C M _ s (hGF a)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
