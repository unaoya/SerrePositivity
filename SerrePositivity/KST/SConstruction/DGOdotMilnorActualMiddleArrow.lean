module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisLaxValue

/-!
概要：共通実長方形の中央辺が保持する全矢印族を、元 dg augmentation で表示する。
方針：元 native／ν 自然性と同じ恒等 lax 同値を、全矢印射影と合成する。
規約：cofiber の比較では代用せず、元全単体と同じ二段評価を保持する。
使われ方：元 LT counit の逆回転との全矢印族比較への入口。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "eL" => dgOdotMilnorRightAxisTargetNativeValueEquivalence R d
local notation "eN" => dgIdentityHomGluingNullLaxEquivalence R (U)
local notation "eB" => dgOdotMilnorRightAxisNativeResolvedValueEquivalence R d
local notation "eC" => dgOdotMilnorRightAxisCompletedGluingEquivalence R d

/-- 概要：同じ中央頂点同値の全矢印射影は元 augmentation の同じ基底評価。
方針：元 native 比較の単位を消去し、恒等 lax の矢印基底変更則を使う。
規約：元全矢印族を保持。使われ方：実中央辺の全矢印比較。 -/
def dgOdotMilnorCompletedGluingNativeArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((eL).hom ≫ (eC).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (Q).obj) (𝟙 (Q).obj))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationArrowFamily.{u, 0} R (U) (U) (U)
      (DGFunctor.id (U)) (DGFunctor.id (U)) ≫
        (ihom (Δ[1] : SSet.{u + 1})).map (eB).hom) := by
  have reassoc {A₀ B₀ C₀ D₀ E₀ : SSet.{u + 1}}
      (a₀ : A₀ ⟶ B₀) (b₀ : B₀ ⟶ C₀) (c₀ : C₀ ⟶ D₀) (d₀ : D₀ ⟶ E₀) :
      (a₀ ≫ b₀) ≫ (c₀ ≫ d₀) = a₀ ≫ ((b₀ ≫ c₀) ≫ d₀) := by
    simp only [Category.assoc]
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence (eB)
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (Q).obj) (𝟙 (Q).obj)
  let f := (eN).hom ≫ t.hom ≫ a
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((eL).hom ≫ (eC).hom ≫ a) f :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((eL).homInvIso.postcomp f)
      (by change ((eL).hom ≫ (eL).inv) ≫ f = _
          exact reassoc (eL).hom (eL).inv ((eN).hom ≫ t.hom) a)
      (Category.id_comp f)
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence_arrow (eB)
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityHomTargetLaxEquivalence_arrow.{u, 0} R (U)
  have hf : f = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationArrowFamily.{u, 0} R (U) (U) (U)
      (DGFunctor.id (U)) (DGFunctor.id (U)) ≫
        (ihom (Δ[1] : SSet.{u + 1})).map (eB).hom := by
    change (eN).hom ≫ (t.hom ≫ a) = _
    exact (congrArg (fun fm => (eN).hom ≫ fm) ht).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun fm => fm ≫ (ihom (Δ[1] : SSet.{u + 1})).map (eB).hom) hn))
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h rfl hf

/-- 概要：実中央辺の全矢印族は同じ元 dg lift の augmentation 全像である。
方針：元 cell native／ν 自然性を全矢印射影で写し、同じ中央比較と合成する。
規約：追加入力なし。元 native 始域と同じ二段評価を保持。
使われ方：元 counit の逆回転との全関手比較の左辺を固定する。 -/
def dgOdotMilnorActualMiddleNativeArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorCellMiddleNativeValueEquivalence R d).hom ≫
      (dgOdotMilnorRightAxisExactMap R d).hom ≫ (eC).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (Q).obj) (𝟙 (Q).obj))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisLift R d) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationArrowFamily.{u, 0} R (U) (U) (U)
        (DGFunctor.id (U)) (DGFunctor.id (U)) ≫
          (ihom (Δ[1] : SSet.{u + 1})).map (eB).hom) := by
  let a := (eC).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (Q).obj) (𝟙 (Q).obj)
  have h₁ := (dgOdotMilnorRightAxisNuComparison R d).postcomp a
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorCompletedGluingNativeArrowComparison R d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisLift R d))
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₁ (Category.assoc _ _ _) (Category.assoc _ _ _)).trans h₂

end SerrePositivity.KST.SConstruction
