module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 小さい dg 入力の対象宇宙の表示
概要：Small.{u} の証拠から入力の対象を Type u に表示し、全 Hom 複体を保持する。
方針：対象の同値に沿って dg 構造を引き戻し、元の入力への準同値を与える。
規約：Perf や native nerve の宇宙縮小を主張しない。使われ方：Perf ラベルの出発圏。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded

/-- 元の小さい dg 入力の対象を Type u に表示する型。 -/
def SmallDGInput (_A : Type u) (D : Type v) [Small.{u} D] : Type u := Shrink.{u} D

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 縮小した対象に対応する、同じ元の dg 圏の対象。 -/
def smallDGInputValue (X : SmallDGInput A D) : D := (equivShrink D).symm X

/-- 対象宇宙の表示を変えても全 Hom 複体・単位・合成は変更しない。 -/
instance smallDGInputEnrichment : DGCategory A (SmallDGInput A D) :=
  ofHomObjects A _ (fun X Y => homObject A D
      (smallDGInputValue A D X) (smallDGInputValue A D Y))
    (fun X => eId (Complex A) (smallDGInputValue A D X))
    (fun X Y Z => eComp (Complex A) (smallDGInputValue A D X)
      (smallDGInputValue A D Y) (smallDGInputValue A D Z))
    (fun X Y => EnrichedCategory.id_comp (smallDGInputValue A D X) (smallDGInputValue A D Y))
    (fun X Y => EnrichedCategory.comp_id (smallDGInputValue A D X) (smallDGInputValue A D Y))
    (fun W X Y Z => EnrichedCategory.assoc (smallDGInputValue A D W)
      (smallDGInputValue A D X) (smallDGInputValue A D Y) (smallDGInputValue A D Z))

/-- 元の入力への dg 関手は各 Hom 複体上で恒等作用する。 -/
def smallDGInputEvaluation : DGFunctor A (SmallDGInput A D) D where
  obj := smallDGInputValue A D
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

/-- 対象の縮小を元へ戻す dg 関手は H⁰ で本質的全射。 -/
instance smallDGInputEvaluationHomotopyEssSurj :
    (smallDGInputEvaluation A D).onHomotopy.EssSurj where
  mem_essImage X := by
    let x := ForgetEnrichment.to (Complex A) X.as
    refine ⟨(toHomotopy A (SmallDGInput A D)).obj
      (ForgetEnrichment.of (Complex A) (equivShrink D x)), ⟨?_⟩⟩
    exact eqToIso (congrArg (fun Y => (toHomotopy A D).obj
      (ForgetEnrichment.of (Complex A) Y)) ((equivShrink D).symm_apply_apply x))

/-- 小さい対象表示から元の dg 入力への実準同値。 -/
lemma smallDGInputEvaluation_quasiEquivalence :
    QuasiEquivalence (smallDGInputEvaluation A D) := by
  refine ⟨?_, inferInstance⟩
  intro X Y
  change QuasiIso (𝟙 _)
  infer_instance

end SerrePositivity.KST.SConstruction
