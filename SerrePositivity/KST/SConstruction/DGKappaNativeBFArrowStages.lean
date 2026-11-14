module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFIntegerComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialOrdinaryMap

/-!
概要：同じ有限 native 入力の通常射に、実 BF 四辺と全正段の作用を回収する。
方針：全 Hom の豊穣作用の単位パラメータを評価する。
規約：旧 K 射を変更しない。使われ方：新旧の整数群作用の可換性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra
open Fibration
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

local instance nativeBFArrowStagesTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：同じ有限 native 射の実 BF スペクトル射。
方針：同じ全 Hom の豊穣作用から通常射を取り出す。
規約：有限入力に限定。使われ方：実 Φ の四辺。 -/
def dgKappaNativeBFFiniteArrow
    {C E : DGKappaNativeBFFiniteInput.{u, v} R D I} (f : C ⟶ E) :
    dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C ⟶
      dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I E :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap (dgKappaNativeBFEnrichedFunctor.{u, v} R D I) f

/-- 概要：同じ実 BF 射の各段は元の全 Hom の段作用を回収する。
方針：実スペクトル写像空間の評価式を単位パラメータで使う。
規約：全段の等式。使われ方：正段比較の通常射自然性。 -/
lemma dgKappaNativeBFFiniteArrow_app
    {C E : DGKappaNativeBFFiniteInput.{u, v} R D I} (f : C ⟶ E) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n) f =
      (dgKappaNativeBFFiniteArrow.{u, v} R D I f).app n := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_of_hom
  let g := dgKappaNativeBFFiniteArrow.{u, v} R D I f
  have h := congrArg (fun k => k ≫ OmegaSpectrum.evaluation _ _ n)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_hom (dgKappaNativeBFEnrichedFunctor.{u, v} R D I) f)
  have hg : eHomEquiv SSet g = OmegaSpectrum.vertexOfHomMap g := by
    change (SSet.unitHomEquiv _).symm
      ((SSet.unitHomEquiv _) (OmegaSpectrum.vertexOfHomMap g)) = _
    exact Equiv.symm_apply_apply _ _
  have he := (congrArg (fun k => k ≫ OmegaSpectrum.evaluation
    (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C)
    (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I E) n) hg).trans
      (OmegaSpectrum.vertexOfHomMap_evaluation g n)
  have ha := (Category.assoc (eHomEquiv SSet f)
    ((dgKappaNativeBFEnrichedFunctor.{u, v} R D I).map C E)
    (OmegaSpectrum.evaluation _ _ n)).trans
      (congrArg (fun k => eHomEquiv SSet f ≫ k)
        (dgKappaNativeBFEnrichedFunctor_evaluation.{u, v} R D I C E n))
  exact ha.symm.trans (h.symm.trans he)

/-- 概要：同じ有限入力の元正段作用は元境界商射の Ex∞ 像。
方針：充満包含と元の境界商の通常射回収を使う。
規約：同じ元完全射を保持。使われ方：旧 BF 射影比較との照合。 -/
lemma dgKappaNativeBFFiniteBoundaryFunctor_hom
    {C E : DGKappaNativeBFFiniteInput.{u, v} R D I} (f : C ⟶ E) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r) f =
      (exInfinityPointedKanMap
        (boundaryReducedRealizationMap r (stableExactInputMap f.hom))).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_of_hom
  change eHomEquiv SSet f.hom ≫ (𝟙 _ ≫
    ((stableBoundaryPointedEnrichedFunctor r).map C.obj E.obj ≫
      exInfinityPointedEnrichedFunctor.map _ _)) = _
  rw [Category.id_comp, ← Category.assoc, stableBoundaryPointedEnrichedFunctor_hom]
  exact coaugmentedPointedEnrichedFunctor_hom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit _

end SerrePositivity.KST.SConstruction
