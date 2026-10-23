module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomComparisonSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomSourceEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEquivalence

/-!
概要：strict 比較空間から実際の Hom 関手の coherent 変換空間への比較射。
方針：標準 Hom の族そのものの pinchedHomMap を使い、豊穣 Hom の比較と端点同型を合成する。
規約：この射の同値性は別の証明課題。独立な比較同値で実際の作用を置き換えない。
使われ方：Hom の族の充満忠実性と、復元同型を全空間側へ回収する主比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {B : SSet.{u}} :
    ∀ X Y : (LeftFibrationObject B)ᵒᵖ, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 標準 Hom の族の写像空間の像の端点を、既存の評価関手の頂点へ揃える。 -/
def relativeHomCoherentEndpointIso {B : SSet.{u}} (a q : LeftFibrationObject B) :
    pinchedHom
      ((leftFibrationHomTestFamily B).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex (Opposite.op q)))
      ((leftFibrationHomTestFamily B).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex (Opposite.op a))) ≅
    pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val)) :=
  eqToIso (congrArg₂ (fun x y ↦ pinchedHom x y)
    (simplicialOverTestFamily_vertex (leftFibrationOverEnriched B) q)
    (simplicialOverTestFamily_vertex (leftFibrationOverEnriched B) a))

/-- 実際の標準 Hom の族による、相対 Hom から coherent な変換への作用。 -/
def relativeHomCoherentComparison {B : SSet.{u}} (a q : LeftFibrationObject B) :
    (SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace q.val.hom a.val.hom) ⟶
      pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val)) :=
  coherentHomComparison (Opposite.op q) (Opposite.op a) ≫
    pinchedHomMap (leftFibrationHomTestFamily B)
      (coherentNerveVertex (Opposite.op q)) (coherentNerveVertex (Opposite.op a)) ≫
        (relativeHomCoherentEndpointIso a q).hom

/-- strict 比較空間から実際の coherent な変換空間への主比較。 -/
def relativeHomComparisonSpaceCoherentMap {B : SSet.{u}} (a q : LeftFibrationObject B) :
    relativeHomComparisonSpace a.val q ⟶
      pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val)) :=
  (relativeHomComparisonSpaceIso a.val q).inv ≫ relativeHomCoherentComparison a q

/-- 実際の比較射の端点の表示変更は、元の coherent 単体を変えない。 -/
lemma relativeHomCoherentComparison_app_val {B : SSet.{u}}
    (a q : LeftFibrationObject B) {n : ℕ}
    (f : ((SSet.uliftFunctor.{u + 1, u}).obj
      (relativeFunctorSpace q.val.hom a.val.hom)) _⦋n⦌) :
    ((relativeHomCoherentComparison a q).app (Opposite.op ⦋n⦌) f).val =
      (leftFibrationHomTestFamily B).app (Opposite.op ⦋n + 1⦌)
        (((coherentHomComparison (Opposite.op q) (Opposite.op a)).app
          (Opposite.op ⦋n⦌) f).val) := by
  let hx := simplicialOverTestFamily_vertex (leftFibrationOverEnriched B) q
  let hy := simplicialOverTestFamily_vertex (leftFibrationOverEnriched B) a
  let s := (pinchedHomMap (leftFibrationHomTestFamily B)
    (coherentNerveVertex (Opposite.op q)) (coherentNerveVertex (Opposite.op a))).app
      (Opposite.op ⦋n⦌)
      ((coherentHomComparison (Opposite.op q) (Opposite.op a)).app (Opposite.op ⦋n⦌) f)
  change (((eqToHom (congrArg₂ (fun x y ↦ pinchedHom x y) hx hy)).app
    (Opposite.op ⦋n⦌)) s).val = s.val
  exact pinchedHom_eqToHom_app_val hx hy s

/-- 関手頂点の評価は、固定標的の相対 Hom の Kan 複体の頂点。 -/
lemma relativeHomCoherentEvaluation_vertex {B : SSet.{u}} (q r : LeftFibrationObject B) :
    (evaluateFunctorAt (coherentNerveVertex r)).app (Opposite.op ⦋0⦌)
      (functorVertex (leftFibrationCoherentEvaluation q.val)) =
    coherentNerveVertex
      ((relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) r).obj
        (Opposite.op q)) := by
  rw [evaluateFunctorAt_functorVertex]
  exact coherentNerveMap_vertex (relativeFunctorEnrichedEvaluation q.val) r

/-- 実際の coherent 変換を固定したテスト標的で評価する写像空間の射。 -/
def relativeHomCoherentEvaluationMap {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val)) ⟶
    pinchedHom
      (coherentNerveVertex
        ((relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) r).obj
          (Opposite.op q)))
      (coherentNerveVertex
        ((relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) r).obj
          (Opposite.op a))) :=
  pinchedHomMap (evaluateFunctorAt (coherentNerveVertex r)) _ _ ≫
    eqToHom (congrArg₂ (fun x y ↦ pinchedHom x y)
      (relativeHomCoherentEvaluation_vertex q r) (relativeHomCoherentEvaluation_vertex a r))

/-- 正規化した評価も、元の coherent 単体に実際の評価を作用させる。 -/
lemma relativeHomCoherentEvaluationMap_app_val {B : SSet.{u}}
    (a q r : LeftFibrationObject B) {n : ℕ}
    (f : (pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val))) _⦋n⦌) :
    ((relativeHomCoherentEvaluationMap a q r).app (Opposite.op ⦋n⦌) f).val =
      (evaluateFunctorAt (coherentNerveVertex r)).app (Opposite.op ⦋n + 1⦌) f.val := by
  let hx := relativeHomCoherentEvaluation_vertex q r
  let hy := relativeHomCoherentEvaluation_vertex a r
  let s := (pinchedHomMap (evaluateFunctorAt (coherentNerveVertex r))
    (functorVertex (leftFibrationCoherentEvaluation q.val))
    (functorVertex (leftFibrationCoherentEvaluation a.val))).app (Opposite.op ⦋n⦌) f
  change (((eqToHom (congrArg₂ (fun x y ↦ pinchedHom x y) hx hy)).app
    (Opposite.op ⦋n⦌)) s).val = s.val
  exact pinchedHom_eqToHom_app_val hx hy s

/-- 主比較をテスト標的で評価すると、固定標的の豊穣 Hom 作用の実際の比較。 -/
lemma relativeHomCoherentComparison_evaluate {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    relativeHomCoherentComparison a q ≫ relativeHomCoherentEvaluationMap a q r =
      coherentHomComparison (Opposite.op q) (Opposite.op a) ≫
        coherentPinchedHomMap
          (relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) r)
          (Opposite.op q) (Opposite.op a) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro f
  apply PinchedHom.Simplex.ext
  change ((relativeHomCoherentEvaluationMap a q r).app (Opposite.op ⦋n⦌)
    ((relativeHomCoherentComparison a q).app (Opposite.op ⦋n⦌) f)).val = _
  rw [relativeHomCoherentEvaluationMap_app_val, relativeHomCoherentComparison_app_val]
  change ((leftFibrationHomTestFamily B ≫ evaluateFunctorAt (coherentNerveVertex r)).app
    (Opposite.op ⦋n + 1⦌) (((coherentHomComparison (Opposite.op q) (Opposite.op a)).app
      (Opposite.op ⦋n⦌) f).val)) = _
  rw [leftFibrationHomTestFamily_evaluate]
  let F := relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) r
  let hx := coherentNerveMap_vertex F (Opposite.op q)
  let hy := coherentNerveMap_vertex F (Opposite.op a)
  let s := (pinchedHomMap (coherentNerveMap F)
    (coherentNerveVertex (Opposite.op q)) (coherentNerveVertex (Opposite.op a))).app
      (Opposite.op ⦋n⦌)
      ((coherentHomComparison (Opposite.op q) (Opposite.op a)).app (Opposite.op ⦋n⦌) f)
  change s.val = (((eqToHom (congrArg₂ (fun x y ↦ pinchedHom x y) hx hy)).app
    (Opposite.op ⦋n⦌)) s).val
  exact (pinchedHom_eqToHom_app_val hx hy s).symm

end SerrePositivity.InfinityCategories
