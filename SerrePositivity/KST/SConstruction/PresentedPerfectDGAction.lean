module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGModel
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation
public import SerrePositivity.DifferentialGraded.Functor.DGClosedComparisonIso

/-! # ラベル付き Perf 模型への厳密 dg 入力の作用
概要：ラベルの延長関手を後合成し、全 Hom を元の合成比較で共役する。
方針：対象を値域の代表へ選び直さず、実閉零同型の共役で dg 関手を構成する。
規約：作用の恒等・合成の厳密保存は別途検証する。使われ方：関手的 Perf 模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D E)

/-- ラベルの出発圏と代表を保持し、厳密 dg 関手を後合成する対象作用。 -/
def presentedPerfectDGActionObject (X : PresentedPerfectDGObject A D) :
    PresentedPerfectDGObject A E where
  source := X.source
  enrichment := X.enrichment
  seed := X.seed
  arrow := X.arrow.comp F

/-- 二回の実延長と、後合成したラベルの評価との元の閉零合成同型。 -/
def presentedPerfectDGActionIso (X : PresentedPerfectDGObject A D) :
    ForgetEnrichment.of (Complex A)
        ((perfectDGExtension A D E F).obj (presentedPerfectDGValue A D X)) ≅
      ForgetEnrichment.of (Complex A)
        (presentedPerfectDGValue A E (presentedPerfectDGActionObject A D E F X)) :=
  perfectDGExtensionCompositionAt A X.source D E X.arrow F X.seed.val

/-- 実 Perf 内で評価したラベル作用。各 Hom は実延長と実閉零同型の共役。 -/
def presentedPerfectDGActionEvaluated :
    DGFunctor A (PresentedPerfectDGObject A D) (PerfectDGModule A E) :=
  dgFunctorClosedConjugate A
    ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F))
    (fun X => presentedPerfectDGValue A E (presentedPerfectDGActionObject A D E F X))
    (presentedPerfectDGActionIso A D E F)

/-- 全次数 Hom 複体上の作用を持つ、ラベル付き Perf の元の dg 関手。 -/
def presentedPerfectDGAction :
    DGFunctor A (PresentedPerfectDGObject A D) (PresentedPerfectDGObject A E) where
  obj := presentedPerfectDGActionObject A D E F
  map := (presentedPerfectDGActionEvaluated A D E F).map
  map_id := (presentedPerfectDGActionEvaluated A D E F).map_id
  map_comp := (presentedPerfectDGActionEvaluated A D E F).map_comp

/-- 評価後の対象作用は、出発圏・元の代表を保つ合成入力の実延長。 -/
lemma presentedPerfectDGAction_obj (X : PresentedPerfectDGObject A D) :
    (presentedPerfectDGAction A D E F).obj X =
      presentedPerfectDGActionObject A D E F X := rfl

/-- 作用の全 Hom は、元の実延長と同じ閉零合成比較の共役で計算する。 -/
lemma presentedPerfectDGAction_map (X Y : PresentedPerfectDGObject A D) :
    (presentedPerfectDGAction A D E F).map X Y =
      (perfectDGExtension A D E F).map
          (presentedPerfectDGValue A D X) (presentedPerfectDGValue A D Y) ≫
        enrichedClosedIsoConjugation (Complex A)
          (presentedPerfectDGActionIso A D E F X)
          (presentedPerfectDGActionIso A D E F Y) := by
  change (𝟙 _ ≫ _) ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- 評価後の全 Hom 作用は、元の実延長を共役した作用と一致する。 -/
lemma presentedPerfectDGAction_evaluation_map (X Y : PresentedPerfectDGObject A D) :
    ((presentedPerfectDGAction A D E F).comp (presentedPerfectDGEvaluation A E)).map X Y =
      (presentedPerfectDGActionEvaluated A D E F).map X Y :=
  Category.comp_id _

/-- 元の実合成同型は、作用後の評価との全 Hom 自然性を満たす。 -/
lemma presentedPerfectDGAction_naturality (X Y : PresentedPerfectDGObject A D) :
    ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F)).map X Y ≫
        eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A)
          ((perfectDGExtension A D E F).obj (presentedPerfectDGValue A D X)))
          (presentedPerfectDGActionIso A D E F Y).hom =
      ((presentedPerfectDGAction A D E F).comp (presentedPerfectDGEvaluation A E)).map X Y ≫
        eHomWhiskerRight (Complex A) (presentedPerfectDGActionIso A D E F X).hom
          (ForgetEnrichment.of (Complex A)
            (presentedPerfectDGValue A E (presentedPerfectDGActionObject A D E F Y))) := by
  rw [presentedPerfectDGAction_evaluation_map]
  exact dgFunctorClosedConjugate_naturality A _ _ _ X Y

/-- ラベル作用と元の実延長の比較は、全次数 Hom に関して自然。 -/
def presentedPerfectDGActionComparison :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj (𝟙_ (Complex A)))
      ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F))
      ((presentedPerfectDGAction A D E F).comp (presentedPerfectDGEvaluation A E)) :=
  dgFunctorClosedComparison A _ _
    (fun X => (presentedPerfectDGActionIso A D E F X).hom)
    (presentedPerfectDGAction_naturality A D E F)

/-- 同じ元の比較を、閉零射圏の自然同型としても保持する。 -/
def presentedPerfectDGActionClosedIso :
    ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F)).onClosed ≅
      ((presentedPerfectDGAction A D E F).comp (presentedPerfectDGEvaluation A E)).onClosed :=
  dgFunctorClosedComparisonIso A _ _ (presentedPerfectDGActionIso A D E F)
    (presentedPerfectDGAction_naturality A D E F)

end SerrePositivity.KST.SConstruction
