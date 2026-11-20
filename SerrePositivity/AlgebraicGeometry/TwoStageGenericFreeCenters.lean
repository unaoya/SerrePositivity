module

public import SerrePositivity.AlgebraicGeometry.BoundaryGenericRankReduction
public import SerrePositivity.AlgebraicGeometry.ConstantGenericRankFreeNeighborhoods
public import SerrePositivity.AlgebraicGeometry.ChartBoundaryRegular

/-!
概要：KST §5、Stacks 0810・0811 の一般階数を分離する中心とチャートごとの自由化中心。
方針：第一段で階数部分を分離し、実分裂と相対平坦性を運んで第二段の実中心を選ぶ。
規約：結論は二段の局所中心の存在であり、一般の平坦化の存在を仮定しない。
使われ方：自由な開部分を作る有限チャート構成を、大域中心への降下へ渡す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：全チャートで基礎環を覆う共通階数の自由化基本開を持つ有限生成中心の存在。
方針：実際の中心、共通階数、元の加群の基底変更と純変換について結論だけをまとめる。
規約：KST §5、Stacks 0810・0811、証明を入力するクラスや追加公理は導入しない。
使われ方：階数を分離した各実チャートに第二段の中心を選ぶ。
-/
def HasBoundaryFreeNeighborhoodCenter (A B : Type u) (M : Type*)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M] (f : A) : Prop :=
  ∃ (J : Ideal A) (s : ℕ),
    J.FG ∧ affineCenterComplement J = PrimeSpectrum.basicOpen f ∧
      ∀ a : J,
        let C := BlowupChartRing J a
        letI : Algebra A C := (chartBaseMap J a).toAlgebra
        BoundaryPureFreeNeighborhoods A B C M (chartBaseMap J a f) s

/--
概要：境界外一般階数が一定なら、自由な基本開近傍を持つ実際の中心が存在する。
方針：境界外一般階数の定義を展開し、有限表示を選ぶ係数中心の存在定理を適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、実分裂を入力する特殊形。
使われ方：第一段の各チャートで第二段の自由化中心を得る。
-/
theorem hasBoundaryFreeNeighborhoodCenter_of_constant_boundaryGenericRank
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)]
    (r : ℕ) (hrank : ∀ P, boundaryGenericRank A B M f P = r) :
    HasBoundaryFreeNeighborhoodCenter A B M f :=
  exists_fg_center_freeNeighborhoods_of_constant_boundary_rank A B e p hpe f hf r hrank

/--
概要：境界外で相対平坦な有限加群に、第一段の有限チャートごとに第二段の自由化中心を選べる。
方針：実際の階数一定化中心を選び、分裂・境界の正則性・境界外の平坦性を各チャートへ運ぶ。
規約：KST §5、Stacks 0811, Lemma 38.30.3 の Noether・実分裂の二段局所構成。
使われ方：一般階数の一定性を仮定せずに自由な基本開部分を得る局所中心を実際に用意する。
-/
theorem exists_twoStage_boundaryFreeNeighborhood_centers
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] :
    ∃ (I : Ideal A) (a : Set.range (boundaryGenericRank A B M f) → I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      (⨆ i, affineBlowupChart I (a i)) = ⊤ ∧
      Pairwise (fun i j => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a j))) ∧
      ∀ i,
        let C := BlowupChartRing I (a i)
        letI : Algebra A C := (chartBaseMap I (a i)).toAlgebra
        let D := C ⊗[A] B
        letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
        HasBoundaryFreeNeighborhoodCenter C D (D ⊗[B] M) (chartBaseMap I (a i) f) := by
  obtain ⟨I, a, hfg, hI, hcover, hdisj, hconst⟩ :=
    exists_fg_center_constant_actual_boundaryGenericRank A B (M := M) e p hpe f hf
  refine ⟨I, a, hfg, hI, hcover, hdisj, ?_⟩
  intro i
  dsimp only
  let C := BlowupChartRing I (a i)
  let : Algebra A C := (chartBaseMap I (a i)).toAlgebra
  let : IsNoetherianRing C := blowupChartRing_isNoetherianRing I (a i)
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let : Module.Flat (Localization.Away (chartBaseMap I (a i) f))
      ((Localization.Away (chartBaseMap I (a i) f)) ⊗[C] (D ⊗[B] M)) :=
    flat_tensorAlgebra_away_of_boundary_flat A C M B f
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  have hfC : IsRegular (chartBaseMap I (a i) f) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (chartBaseMap_nonZeroDivisors I (a i) (isRegular_iff_mem_nonZeroDivisors.mp hf))
  exact hasBoundaryFreeNeighborhoodCenter_of_constant_boundaryGenericRank C D e' p' hs
    (chartBaseMap I (a i) f) hfC i.val (hconst i)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
