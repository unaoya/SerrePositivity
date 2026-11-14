module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterValueEquivalences
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuSourceSquare
public import SerrePositivity.KST.SConstruction.DGKNativeNuNaturality

/-!
概要：元実始域外面の包含を、元 LT 外周の包含へ全関手同型で比較する。
方針：元 cell 比較の厳密な増大可換式と同じ native／ν 全自然性を使う。
規約：元始域の増大屋根・元の合成包含を保持する。
使われ方：実外周の指定包含境界と全四角形比較の第一側面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d))
local notation "B" => DGOdotGluing R d
local notation "TA" => DGCategoryCellResolution.Source R (A)
local notation "TB" => DGCategoryCellResolution.Source R (B)
local notation "F" => dgOdotMilnorSourceCellComparison R d
local notation "E₀" => dgOdotMilnorSourceCellNativeValueEquivalence R d
local notation "E₁" => dgOdotMilnorCellMiddleNativeValueEquivalence R d
local notation "a" => dgOdotMilnorOuterSourceValueEquivalence R d
local notation "b" => dgOdotMilnorOuterMiddleValueEquivalence R d
local notation "i" => dgOdotMilnorNuSourceInclusion R d
local notation "j" => dgOdotMilnorLaxInclusion R d
local instance outerSource_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (A) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSource_isDGPretriangulated R d
local instance outerMiddle_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance outerSourceCell_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (TA) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (A)
local instance outerMiddleCell_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (TB) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (B)

/-- 概要：元実外周の S 合成包含は同じ元 cell 比較の入力辺そのもの。
方針：宇宙持ち上げの合成則と元核因子化の回収を使う。
規約：全 dg 関手の等号。使われ方：実包含の native 自然性。 -/
lemma dgOdotMilnorOuterInclusionInputMap :
    dgOdotMilnorSourceKernelInputMap R d ≫ dgOdotMilnorFlatKernelInputMap R d =
      dgKNativeInputMap R (TA) (TB) (F) := by
  apply ULift.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor (dgOdotMilnorSourceKernelDGMap R d)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor _) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor (F)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp, dgOdotMilnorSourceKernelDGMap_inclusion]

/-- 概要：元実外周包含は同じ cell 比較の native／ν 自然性を保持する。
方針：同じ入力辺回収後に既存の全自然性を適用する。
規約：元包含・元頂点比較を保持。使われ方：実外周の指定第一側面。 -/
def dgOdotMilnorOuterInclusionNativeComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((E₀).hom ≫ (i).hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ (E₁).hom) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((E₀).hom ≫ (dgKInputNuMap R
    (dgOdotMilnorSourceKernelInputMap R d ≫ dgOdotMilnorFlatKernelInputMap R d)).hom) _
  rw [dgOdotMilnorOuterInclusionInputMap]
  exact dgKNativeNuNaturality R (TA) (TB) (F)

/-- 概要：元 cell 包含と増大を通る全図式は元 lax 包含を厳密に回収する。
方針：同じ cell 比較の増大可換式を nerve の合成保存で写す。
規約：元 native 始域を保持。使われ方：固定 ν 頂点比較後の包含照合。 -/
lemma dgOdotMilnorOuterInclusionAugmentation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (B)).hom ≫
      (dgOdotMilnorNativeLaxEquivalence R d).hom) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (A)).hom ≫ (j).hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (B)) ≫
    (dgOdotMilnorNativeLaxEquivalence R d).hom) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (A)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)) ≫
          (dgOdotMilnorNativeLaxEquivalence R d).hom)
  let δ := DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)
  let L : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (B) ⟶ (dgOdotMilnorLaxCategory R d).obj :=
    (dgOdotMilnorNativeLaxEquivalence R d).hom
  have hc : (F).comp (DGCategoryCellResolution.augmentation R (B)) =
      (DGCategoryCellResolution.augmentation R (A)).comp δ :=
    DGCategoryCellResolution.comparisonFunctor_augmentation R (A) (B) δ
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (B))) ≫ L :=
      (Category.assoc _ _ _).symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((F).comp (DGCategoryCellResolution.augmentation R (B))) ≫ L :=
      congrArg (fun k => k ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (F)
        (DGCategoryCellResolution.augmentation R (B))).symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((DGCategoryCellResolution.augmentation R (A)).comp δ) ≫ L :=
      congrArg (fun k : DGFunctor R (TA) (B) => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map k ≫ L) hc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (A)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map δ) ≫ L :=
      congrArg (fun k => k ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp
        (DGCategoryCellResolution.augmentation R (A)) δ)
    _ = _ := Category.assoc _ _ _

/-- 概要：元実外周の包含辺と元 LT 包含は同じ指定二頂点比較で全自然に可換。
方針：元 cell 比較の native 自然性と同じ増大可換式を比較同値で反映する。
規約：元始域の増大屋根を保持。使われ方：実外周の包含全比較。 -/
def dgOdotMilnorOuterInclusionComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((i).hom ≫ (b).hom) ((a).hom ≫ (j).hom) := by
  apply ((E₀).isQCatEquivalence.precompose (dgOdotMilnorLaxCategory R d).obj).isFullyFaithful.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((E₀).hom ≫ ((i).hom ≫ (b).hom))
    ((E₀).hom ≫ ((a).hom ≫ (j).hom))
  have h₁ := (dgOdotMilnorOuterInclusionNativeComparison R d).postcomp (b).hom
  have h₂ := (dgOdotMilnorOuterMiddleValueEquivalence_native R d).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F))
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₁ (Category.assoc _ _ _) (Category.assoc _ _ _)).trans h₂
  have h₄ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₃ rfl (dgOdotMilnorOuterInclusionAugmentation R d)
  have h₅ := (dgOdotMilnorOuterSourceValueEquivalence_native R d).postcomp (j).hom
  exact h₄.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₅ (Category.assoc _ _ _) rfl).symm
end SerrePositivity.KST.SConstruction
