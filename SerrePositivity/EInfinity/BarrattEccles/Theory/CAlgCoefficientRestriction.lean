module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraCoefficientRestriction
public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.EInfinity.FrameHom.MixedNerveNatTrans
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
# Barratt–Eccles の導来係数制限

## 概要
HA §3.2.2 の係数制限を既存の Barratt–Eccles の局所化に降ろす。

## 方針
元の cofibrant 入力に厳密な係数制限を施し、擬同型を反転する関手として延長する。

## 規約
係数制限後の代数に cofibrancy を仮定しない。

## 使われ方
M13 の係数制限関手と元の代数からの比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet SimplicialLocalization
open SerrePositivity.InfinityCategories _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 厳密代数への成分が擬同型である自然変換を、全関手の同型に送る。 -/
def algebraCAlgSourceNatTransIso {I : Type (u + 1)} [Category.{u} I]
    {F G : I ⥤ (operad A).Algebra} (η : F ⟶ G) (hη : ∀ i, QuasiIso (η.app i).hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap F ≫ algebraCAlgSource A) (nerveMap G ≫ algebraCAlgSource A) := by
  let H := _root_.SerrePositivity.SimplicialModel.HomotopyClasses.postHomotopy (algebraCAlgSource A) (FrameHom.MixedNerve.homotopy η)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy H
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).toTruncated)
    (f := ((nerve.edgeMk (η.app i)).map (algebraCAlgSource A)).toTruncated)
    (congrArg ((algebraCAlgSource A).app (Opposite.op ⦋1⦌))
      (FrameHom.MixedNerve.homotopy_component η i))).mpr
        (algebraCAlgSource_map_weak A (η.app i) (hη i))

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- cofibrant 入力の DK nerve から、元の全代数の nerve への包含。 -/
def cofibrantAlgebraInclusionNerve :
    nerve (cofibrantAlgebraRelativeCategory A).category ⟶ nerve (operad A).Algebra where
  app _ := ↾fun Γ => Γ ⋙ cofibrantAlgebraDKInclusion A
  naturality _ _ _ := rfl

/-- nerve での包含は元の代数射を保つ。 -/
lemma cofibrantAlgebraInclusionNerve_mk₁
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (g : X ⟶ Y) :
    (cofibrantAlgebraInclusionNerve A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ g) =
      ComposableArrows.mk₁ ((cofibrantAlgebraDKInclusion A).map g) := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 関手的置換を包含すると、元の全代数の自己関手となる。 -/
lemma algebraCAlgReplacementNerve_inclusion :
    algebraCAlgReplacementNerve A ≫ cofibrantAlgebraInclusionNerve A =
      nerveMap (framedLimitProbeFunctor A) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ cofibrantAlgebraDKReplacement A) ⋙ cofibrantAlgebraDKInclusion A = _
  rw [Functor.assoc, cofibrantAlgebraDKReplacement_comp_inclusion]
  rfl

/-- 局所化前の cofibrant 代数に厳密な係数制限を適用した関手。 -/
def cAlgCoefficientRestrictionSource :
    nerve (cofibrantAlgebraRelativeCategory T).category ⟶ CAlg_R S :=
  cofibrantAlgebraInclusionNerve T ≫ nerveMap (coefficientRestriction f) ≫ algebraCAlgSource S

/-- 係数制限の後に局所化すると、元の擬同型を反転する。 -/
lemma cAlgCoefficientRestrictionSource_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (cAlgCoefficientRestrictionSource f)
      (weakNerveEdges (cofibrantAlgebraRelativeCategory T)) := by
  intro σ hσ
  obtain ⟨X, Y, g, hg, rfl⟩ := hσ
  let F := cofibrantAlgebraDKInclusion T ⋙ coefficientRestriction f
  have hq : QuasiIso (F.map g).hom := coefficientRestriction_map_quasiIso f _
    ((cofibrantAlgebraRelativeCategory_weakEquivalences_iff T g).mp hg)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ g)).map
      ((truncation 2).map (cAlgCoefficientRestrictionSource f)))
    (f := ((nerve.edgeMk (F.map g)).map (algebraCAlgSource S)).toTruncated) ?_).mpr
    (algebraCAlgSource_map_weak S (F.map g) hq)
  change (algebraCAlgSource S).app (Opposite.op ⦋1⦌)
      ((nerveMap (coefficientRestriction f)).app (Opposite.op ⦋1⦌)
        ((cofibrantAlgebraInclusionNerve T).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ g))) =
    (algebraCAlgSource S).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (F.map g))
  rw [cofibrantAlgebraInclusionNerve_mk₁, nerveMap_app_mk₁]
  rfl

/-- 任意の環準同型に沿う Barratt–Eccles の導来係数制限は、元の局所化から延長できる。 -/
lemma cAlgCoefficientRestriction_exists :
    ∃ R : CAlg_R T ⟶ CAlg_R S,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgLocalizationSource T ≫ R)
        (cAlgCoefficientRestrictionSource f)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.localization_extension_exists (cAlgLocalizationSource T)
    (weakNerveEdges (cofibrantAlgebraRelativeCategory T)) (cAlgLocalizationSource_inverts T)
    (cAlgLocalizationPrecomposition_isQCatEquivalence T (CAlg_R S))
    (cAlgCoefficientRestrictionSource f) (cAlgCoefficientRestrictionSource_inverts f)

/-- HA §3.2.2 の係数制限関手を既存の CAlg 上に実現する。 -/
def barrattEcclesRestrict (f : S →+* T) : CAlg_R T ⟶ CAlg_R S :=
  Classical.choose (cAlgCoefficientRestriction_exists f)

/-- 係数制限の延長に付随する、cofibrant 入力上の全関手の比較。 -/
def barrattEcclesRestrict_cofibrantIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgLocalizationSource T ≫ barrattEcclesRestrict f)
      (cAlgCoefficientRestrictionSource f) :=
  (Classical.choose_spec (cAlgCoefficientRestriction_exists f)).some

/-- 導来係数制限と厳密な係数制限の全代数上の自然比較。 -/
def barrattEcclesRestrict_sourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (algebraCAlgSource T ≫ barrattEcclesRestrict f)
      (nerveMap (coefficientRestriction f) ≫ algebraCAlgSource S) := by
  let η := Functor.whiskerRight (framedLimitProbeComparisonNatTrans T) (coefficientRestriction f)
  have hη (X : (operad T).Algebra) : QuasiIso (η.app X).hom :=
    coefficientRestriction_map_quasiIso f _ (framedLimitProbeComparison_quasiIso T X)
  have e := (barrattEcclesRestrict_cofibrantIso f).precomp (algebraCAlgReplacementNerve T)
  have he : algebraCAlgReplacementNerve T ≫ cAlgCoefficientRestrictionSource f =
      nerveMap (framedLimitProbeFunctor T ⋙ coefficientRestriction f) ≫ algebraCAlgSource S := by
    rw [cAlgCoefficientRestrictionSource, ← Category.assoc, ← Category.assoc,
      algebraCAlgReplacementNerve_inclusion]
    rfl
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (algebraCAlgSourceNatTransIso S η hη) he.symm (by rw [Functor.id_comp]))
    (by simp only [algebraCAlgSource, Category.assoc]) rfl

end SerrePositivity.EInfinity.BarrattEccles
