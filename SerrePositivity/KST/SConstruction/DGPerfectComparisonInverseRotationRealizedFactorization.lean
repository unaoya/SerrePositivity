module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationPerfectRealized
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInput

/-!
概要：元二段 Perf realization を、同じ実逆回転・実差・実像包含の厳密合成として回収する。
方針：同じ実差の全像包含回収と厳密 dg 合成の結合則を使用する。
規約：元実対象・元二段評価・全 Hom 作用を変更しない。
使われ方：外周の実合成辺を元 resolved 射影の保存済み二段全比較へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E P : Type (u + 1))
  [DGCategory R E] [Small.{u} E] [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (PerfectDGModule R E))
  (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G)
local notation "T" => DGPerfectComparisonBase R E F G
local notation "U" => DGPerfectComparisonInverseRotationBase R E F G
local notation "I" => DGFunctor.id (T)
local notation "LU" => DGIdentityHomGluing R (U)
local notation "LT" => DGIdentityHomGluing R (T)
local notation "Cn" => dgHomGluingConeFunctor R (U) (U) (U)
  (DGFunctor.id (U)) (DGFunctor.id (U))
local notation "iD" => dgSmallPerfectEnvelopeInclusion R (U) (LU) (EnrichedFunctor.obj (Cn))
local notation "δ" => dgIdentityHomGluingDifference R (U)
local notation "J1" => dgSmallPerfectEnvelopeInclusion R (T) ((LT) ⊕ (LT))
  (dgHomGluingLoopConeFamily R (T) (T) (T) (I) (I))
local notation "J2" => dgSmallPerfectEnvelopeInclusion R E (P ⊕ P)
  (dgPerfectComparisonFamily R E F G)
local notation "VP1" => dgPerfectRealizationPerfect R (U) (T) (J1)
local notation "VP2" => dgPerfectRealizationPerfect R (T) E (J2)

/-- 概要：元二段全族は実中央射・実差・元実像包含と同じ二段評価の厳密合成。
方針：元実逆回転と実像包含の定義を保って結合則だけで回収する。
規約：全 dg 関手の等号。使われ方：共通実長方形の外周商辺の全比較。 -/
lemma dgPerfectComparisonInverseRotationPerfectRealizedFamily_factorization :
    dgPerfectComparisonInverseRotationPerfectRealizedFamily R E F G τ =
      ((((dgPerfectComparisonInverseRotationFunctor R E F G τ).comp (δ)).comp (iD)).comp
        (VP1)).comp (VP2) := by
  let H := dgPerfectComparisonHomGluingFunctor R E F G τ
  let IR := dgHomGluingInverseRotationFunctor R (T) (T) (T) (I) (I)
  have hδ : (δ).comp (iD) = (Cn) :=
    dgSmallPerfectFunctorImageLift_inclusion R (LU) (U) (Cn)
  change ((H.comp ((IR.comp (Cn)).comp (VP1))).comp (VP2)) =
    ((((H.comp IR).comp (δ)).comp (iD)).comp (VP1)).comp (VP2)
  rw [strictDGFunctor_comp_assoc (H.comp IR) (δ) (iD), hδ]
  simp only [strictDGFunctor_comp_assoc]

/-- 概要：同じ二段全族の native nerve は元実合成の五辺を全回収する。
方針：元 dg 関手等号と native nerve の厳密合成則を使用する。
規約：元全関手の等号。使われ方：元実合成の評価と二段全比較の正規化。 -/
lemma dgPerfectComparisonInverseRotationPerfectRealizedFamily_native_factorization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectComparisonInverseRotationPerfectRealizedFamily R E F G τ) =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectComparisonInverseRotationFunctor R E F G τ) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (iD)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP2) := by
  rw [dgPerfectComparisonInverseRotationPerfectRealizedFamily_factorization,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]

end SerrePositivity.KST.SConstruction
