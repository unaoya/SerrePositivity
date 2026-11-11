module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisRealizationValue
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCellNuComparison
public import SerrePositivity.KST.SConstruction.FunctorIsoEquivalenceReflection

/-!
概要：共通実 S 長方形の中央射と実差の合成を、元 resolved 射影の固定 ν 辺へ全比較する。
方針：同じ二段 realization の厳密分解・元指定評価比較・元商 Yoneda 比較を合成する。
規約：元始域・実中央射・元実 cone 差・指定完備化を保持し、残終端で置換しない。
使われ方：外周認証と上下指定二単体付き全長方形比較の商側境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "τ" => dgOdotMilnorRightAxisQuotientComparison R d
local notation "T" => DGPerfectComparisonBase R (Q) (F) (G)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "LT" => DGIdentityHomGluing R (T)
local notation "LU" => DGIdentityHomGluing R (U)
local notation "Cn" => dgHomGluingConeFunctor R (U) (U) (U)
  (DGFunctor.id (U)) (DGFunctor.id (U))
local notation "iD" => dgSmallPerfectEnvelopeInclusion R (U) (LU) (EnrichedFunctor.obj (Cn))
local notation "J1" => dgSmallPerfectEnvelopeInclusion R (T) ((LT) ⊕ (LT))
  (dgHomGluingLoopConeFamily R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T)))
local notation "J2" => dgSmallPerfectEnvelopeInclusion R (Q) ((P) ⊕ (P))
  (dgPerfectComparisonFamily R (Q) (F) (G))
local notation "VP1" => dgPerfectRealizationPerfect R (U) (T) (J1)
local notation "VP2" => dgPerfectRealizationPerfect R (T) (Q) (J2)
local notation "H" => dgOdotMilnorRightAxisLift R d
local notation "δ" => dgOdotMilnorRightAxisIdentityDifference R d
local notation "PF" => dgOdotMilnorRightAxisInverseRotationPerfectRealizedFamily R d
local notation "eD" => dgOdotMilnorRightAxisIdentityDifferenceNativeValueEquivalence R d
local notation "eT" => dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d

/-- 概要：元実合成の native 全辺は同じ D-21 完備化を伴う元 resolved 射影へ全比較される。
方針：元指定終域評価を二段全族へ運び、保存済み元商 Yoneda 全比較と貼る。
規約：元実射・元評価・同じ完備化を保持。使われ方：固定 ν の外周商辺比較の中間面。 -/
def dgOdotMilnorRightAxisCompositeNativeNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ) ≫ (eD).hom ≫ (eT).hom)
    ((dgOdotMilnorCellNativeProjection R d).hom ≫ (dgOdotMilnorCompletion R d).hom) := by
  have assocTail {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : SSet.{u + 1}}
      (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
      (a₃ : X₃ ⟶ X₄) (a₄ : X₄ ⟶ X₅) (a₅ : X₅ ⟶ X₆) :
      (a₀ ≫ a₁) ≫ (a₂ ≫ a₃ ≫ a₄ ≫ a₅) =
        ((((a₀ ≫ a₁) ≫ a₂) ≫ a₃) ≫ a₄) ≫ a₅ := by
    simp only [Category.assoc]
  let vQ := (dgKNativePerfectValueEquivalence R (Q)).hom
  have hPF : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (PF) =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (iD)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP2) :=
    dgPerfectComparisonInverseRotationPerfectRealizedFamily_native_factorization
      R (Q) (P) (F) (G) (τ)
  have htarget : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (iD) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP2) ≫ vQ) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (PF) ≫ vQ :=
    (assocTail _ _ _ _ _ _).trans (congrArg (fun fm => fm ≫ vQ) hPF).symm
  have e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorRightAxisDifferenceRealizationNuComparison R d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ)))
    (Category.assoc _ _ _) htarget
  exact e.trans (dgOdotMilnorRightAxisInverseRotationRealizedNuComparison R d)

/-- 概要：同じ固定 ν の実中央辺・実差の合成は元 cell 商射影と全関手同型。
方針：元二辺の ν 自然性と元実全評価を貼り、同じ cell 始域同値で反映する。
規約：Milnor 条件の追加入力なし。元 S 辺と元指定終域同値を保持する。
使われ方：共通実外周の指定商辺、元上下二単体付き全比較の接続。 -/
def dgOdotMilnorRightAxisCompositeNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKInputNuMap R (dgOdotMilnorRightAxisInputMap R d)).hom ≫
      (dgKInputNuMap R (dgOdotMilnorRightAxisIdentityDifferenceInputMap R d)).hom ≫ (eT).hom)
    (dgOdotMilnorCellProjectionExactMap R d).hom := by
  let a := (dgKInputNuMap R (dgOdotMilnorRightAxisInputMap R d)).hom
  let b := (dgKInputNuMap R (dgOdotMilnorRightAxisIdentityDifferenceInputMap R d)).hom
  let eP := dgOdotMilnorCellMiddleNativeValueEquivalence R d
  let eL := dgOdotMilnorRightAxisTargetNativeValueEquivalence R d
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eP.hom ≫ a ≫ b ≫ (eT).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ eL.hom ≫ b ≫ (eT).hom) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((dgOdotMilnorRightAxisNuComparison R d).postcomp (b ≫ (eT).hom))
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  have h2 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ eL.hom ≫ b ≫ (eT).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ) ≫ (eD).hom ≫ (eT).hom) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp ((dgOdotMilnorRightAxisIdentityDifferenceNuComparison R d).postcomp
        (eT).hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H)))
      (congrArg (fun fm => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ fm) (Category.assoc _ _ _))
      (congrArg (fun fm => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H) ≫ fm) (Category.assoc _ _ _))
  exact functorIsoReflectPreEquivalence eP
    (h1.trans (h2.trans ((dgOdotMilnorRightAxisCompositeNativeNuComparison R d).trans
      (dgOdotMilnorCellProjectionNuComparison R d).symm)))

end SerrePositivity.KST.SConstruction
