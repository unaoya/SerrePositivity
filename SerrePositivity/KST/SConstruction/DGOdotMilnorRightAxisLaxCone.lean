module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisLaxValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityNativeConeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityLaxArrowBaseCofiber

/-!
概要：実右軸の同じ cone 差を、元 resolved 商値の絶対恒等 lax 差へ全比較する。
方針：元 native cone 比較を同じ実全像評価・元二段評価で運ぶ。
規約：対角と同じ中央同値を使い、元実 cone と指定終域評価を保持する。
使われ方：共通実右面の商境界と絶対恒等面への全図式比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "L" => DGOdotMilnorRightAxisTarget R d
local notation "D" => DGOdotMilnorRightAxisIdentityDifference R d
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "F" => dgHomGluingConeFunctor R (U) (U) (U)
  (DGFunctor.id (U)) (DGFunctor.id (U))
local notation "δ" => dgOdotMilnorRightAxisIdentityDifference R d
local notation "eL" => dgOdotMilnorRightAxisTargetNativeValueEquivalence R d
local notation "eD" => dgOdotMilnorRightAxisIdentityDifferenceNativeValueEquivalence R d
local notation "eB" => dgOdotMilnorRightAxisBaseValueEquivalence R d
local notation "eN" => dgIdentityHomGluingNullLaxEquivalence R (U)
local notation "eQ" => dgOdotMilnorRightAxisNativeResolvedValueEquivalence R d
local notation "eT" => dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d
/-- 概要：同じ実逆回転基底の native nerve の安定性を充足する。
方針：元基底の前三角性を D 正本の native 安定性へ明示的に渡す。
規約：新しい安定模型を選ばない。使われ方：同じ native cone 差の全比較。 -/
lemma dgOdotMilnorRightAxisNativeStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U)) :=
  @_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R _ (U) _ _
    (dgOdotMilnorRightAxisBase_pretriangulated R d)

/-- 概要：同じ実 native 基底の恒等 lax 矢印族の選択差。
方針：既存の安定性証拠を明示的に渡して同じ cofiber 全族を読む。
規約：差を選び直さない。使われ方：実 cone 比較の native 側。 -/
def dgOdotMilnorRightAxisNativeLaxDifference :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U))) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U) :=
  @_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U)) inferInstance
    (dgOdotMilnorRightAxisNativeStable R d) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U))) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U))))

/-- 概要：元 native 恒等差と元実 cone 差は同じ resolved 商値への全比較を持つ。
方針：D の全 cone 比較と元実像評価の全回収を合成する。
規約：元二段評価を保持。使われ方：固定 ν の商辺の中央比較。 -/
def dgOdotMilnorRightAxisNativeResolvedConeComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((eN).hom ≫ dgOdotMilnorRightAxisNativeLaxDifference R d ≫ (eQ).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ) ≫ (eD).hom ≫ (eT).hom) := by
  let v := (dgKNativePerfectValueEquivalence R (U)).hom
  let z : U := dgSmallPerfectEnvelopeZero R _ _ _
  have hz : IsZero (ForgetEnrichment.of (Complex R) z) :=
    dgSmallPerfectEnvelopeZero_isZero R _ _ _
  have hc := @dgKNativeValueComparison_eq R _ (U) _ _
    (dgOdotMilnorRightAxisBase_pretriangulated R d)
  have hn := (@_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeConeComparison R _ (U) _ _
    (dgOdotMilnorRightAxisBase_pretriangulated R d)
    (dgOdotMilnorRightAxisBase_complete R d) z hz).postcomp (v ≫ (eB).hom)
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (((eN).hom ≫ dgOdotMilnorRightAxisNativeLaxDifference R d) ≫ (eQ).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ v ≫ (eB).hom) := by
    refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq hn ?_ rfl
    change ((eN).hom ≫ _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (U)) ≫
      (v ≫ (eB).hom)) = ((eN).hom ≫ _) ≫ ((eQ).hom)
    exact congrArg (fun k => ((eN).hom ≫ _) ≫ k)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ (eB).hom) hc.symm))
  have imageRecovery (T E : Type (u + 1)) [DGCategory R T] [Small.{u} T]
      [DGCategory R E] [Small.{u} E] (G : DGFunctor R E (PerfectDGModule R T)) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectFunctorImageLift R E T G) ≫
        (dgSmallPerfectEnvelopeNerveEquivalence R T E G.obj).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectFunctorImageLift R E T G) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectEnvelopeInclusion R T E G.obj) = _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _).symm.trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectFunctorImageLift_inclusion R E T G))
  have heval : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ) ≫
      (dgSmallPerfectEnvelopeNerveEquivalence R (U) (L) (F).obj).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) :=
    imageRecovery (U) (L) (F)
  have hright := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    ((dgOdotMilnorRightAxisIdentityDifferenceValueEquivalence_native R d).postcomp (eB).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ))
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ) ≫ (eD).hom ≫ (eT).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ v ≫ (eB).hom) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq hright
      (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ) ≫ k) (Category.assoc _ _ _))
      ((congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ) ≫ k) (Category.assoc _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ v ≫ (eB).hom) heval)))
  exact hleft.trans hr.symm

/-- 概要：元固定 ν の実 cone 差は同じ中央同値の下で絶対恒等 lax 差と全比較される。
方針：元 native cone 全比較・lax 基底変更・元差辺の ν 自然性を貼り、元同値で反映する。
規約：元商辺と指定終域同値を保持。使われ方：実右面の指定商境界。 -/
def dgOdotMilnorRightAxisCompletedDifferenceComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorRightAxisCompletedGluingEquivalence R d).hom ≫
      (exactLaxDifference (𝟙 (Q)) (𝟙 (Q))).hom)
    ((dgKInputNuMap R (dgOdotMilnorRightAxisIdentityDifferenceInputMap R d)).hom ≫
      (eT).hom) := by
  let g := (dgOdotMilnorRightAxisCompletedGluingEquivalence R d).hom
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence (eQ)
  let q := (exactLaxDifference (𝟙 (Q)) (𝟙 (Q))).hom
  have cancel {X Y Z : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
      [Quasicategory Z] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) (k : X ⟶ Z) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ (e.inv ≫ k)) k :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.homInvIso.postcomp k) (Category.assoc _ _ _)
      (Category.id_comp k)
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((eL).hom ≫ g ≫ q) ((eN).hom ≫ t.hom ≫ q) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((cancel (eL) ((eN).hom ≫ t.hom)).postcomp q)
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (@_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseCofiberComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U)) (Q).obj
    inferInstance (Q).isQuasicategory (dgOdotMilnorRightAxisNativeStable R d)
    (Q).isStable (eQ)) (eN).hom
  have h₃ := dgOdotMilnorRightAxisNativeResolvedConeComparison R d
  have h₄ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgOdotMilnorRightAxisIdentityDifferenceNuComparison R d).postcomp (eT).hom)
    (Category.assoc _ _ _) (Category.assoc _ _ _)
  exact functorIsoReflectPreEquivalence (eL) (h₁.trans (h₂.trans (h₃.trans h₄.symm)))

end SerrePositivity.KST.SConstruction
