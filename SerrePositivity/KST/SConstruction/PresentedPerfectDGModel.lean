module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionComposition
public import SerrePositivity.KST.SConstruction.PerfectDGStableModel

/-! # 出発圏と延長を保持する Perf の対象模型
概要：出発圏の小さい代表と厳密 dg 関手を保持し、実延長で Hom 複体を評価する。
方針：代表選択を値域で繰り返さず、評価対象の全 Hom・単位・合成をそのまま使う。
規約：対象は Type (max (u+1) v)。Small.{u} や nerve の宇宙縮小は主張しない。
使われ方：厳密 dg 入力に関手的な Perf 模型と元の実 Perf の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded

/-- 小さい出発圏・その代表・厳密 dg 延長を保持する対象。 -/
structure PresentedPerfectDGObject (A : Type u) [CommRing A]
    (D : Type v) [DGCategory A D] where
  source : Type u
  enrichment : DGCategory A source
  seed : @SmallPerfectDGModuleOver A _ source enrichment (inferInstance : Small.{u} source) Set.univ
  arrow : @DGFunctor A _ source D enrichment _

attribute [instance] PresentedPerfectDGObject.enrichment

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- ラベルを保持した対象を、元の実 Perf dg 延長で評価する。 -/
def presentedPerfectDGValue (X : PresentedPerfectDGObject A D) : PerfectDGModule A D :=
  (perfectDGExtension A X.source D X.arrow).obj X.seed.val

/-- 全次数 Hom 複体・単位・合成を実 Perf の評価から引き戻す。 -/
instance presentedPerfectDGEnrichment : DGCategory A (PresentedPerfectDGObject A D) :=
  ofHomObjects A _ (fun X Y => homObject A (PerfectDGModule A D)
      (presentedPerfectDGValue A D X) (presentedPerfectDGValue A D Y))
    (fun X => eId (Complex A) (presentedPerfectDGValue A D X))
    (fun X Y Z => eComp (Complex A) (presentedPerfectDGValue A D X)
      (presentedPerfectDGValue A D Y) (presentedPerfectDGValue A D Z))
    (fun X Y => EnrichedCategory.id_comp
      (presentedPerfectDGValue A D X) (presentedPerfectDGValue A D Y))
    (fun X Y => EnrichedCategory.comp_id
      (presentedPerfectDGValue A D X) (presentedPerfectDGValue A D Y))
    (fun W X Y Z => EnrichedCategory.assoc (presentedPerfectDGValue A D W)
      (presentedPerfectDGValue A D X) (presentedPerfectDGValue A D Y)
      (presentedPerfectDGValue A D Z))

/-- 評価は元の実 Perf に対して各 Hom 複体上で恒等作用する。 -/
def presentedPerfectDGEvaluation :
    DGFunctor A (PresentedPerfectDGObject A D) (PerfectDGModule A D) where
  obj := presentedPerfectDGValue A D
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

/-- 評価の全 Hom 上の作用は恒等射。 -/
lemma presentedPerfectDGEvaluation_map (X Y : PresentedPerfectDGObject A D) :
    (presentedPerfectDGEvaluation A D).map X Y = 𝟙 _ := rfl

/-- 評価は全 Hom の擬同型を与える。 -/
lemma presentedPerfectDGEvaluation_quasiIso (X Y : PresentedPerfectDGObject A D) :
    QuasiIso ((presentedPerfectDGEvaluation A D).map X Y) := by
  change QuasiIso (𝟙 _)
  infer_instance

end SerrePositivity.KST.SConstruction
