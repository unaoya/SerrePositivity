module

public import SerrePositivity.InfinityCategories.F1.SimplicialPairLeftInclusion
public import SerrePositivity.InfinityCategories.F1.SimplicialOverTestFamily

/-!
概要：標準 Hom の反変な族を固定したテスト標的で評価する。
方針：共同評価を積の第一の因子へ制限し、curry の頂点評価を使う。
規約：評価の等式は始域の全対象・全高次を保つ厳密な等式。
使われ方：strict 比較空間から実際の coherent 変換空間への比較の評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- テスト標的を固定した、始域に反変な相対 Hom の豊穣評価。 -/
def relativeHomSourceEvaluationEnriched {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) (r : LeftFibrationObject B) :
    EnrichedFunctor SSet.{u} Cᵒᵖ KanObject.{u} :=
  (simplicialPairLeftInclusion Cᵒᵖ r).comp SSet (simplicialOverTestBifunctor F)

/-- Hom 関手の族をテスト標的で評価すると、始域に反変な相対 Hom の共同評価。 -/
lemma simplicialOverTestFamily_evaluate {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) (r : LeftFibrationObject B) :
    simplicialOverTestFamily F ≫ evaluateFunctorAt (coherentNerveVertex r) =
      coherentNerveMap (relativeHomSourceEvaluationEnriched F r) := by
  rw [simplicialOverTestFamily, curry_evaluateFunctorAt_vertex]
  change (lift (SSet.const (coherentNerveVertex r)) (𝟙 (SimplicialNerve Cᵒᵖ)) ≫
    (β_ (LeftFibrationInfinity B) (SimplicialNerve Cᵒᵖ)).hom) ≫
      simplicialPairNerveFrom Cᵒᵖ (LeftFibrationObject B) ≫ simplicialOverJointTest F = _
  dsimp only [LeftFibrationInfinity]
  rw [lift_braiding_hom, ← Category.assoc, simplicialPairNerveFrom_left]
  rfl

/-- 標準 Hom の族の評価も、同じ相対 Hom の実際の豊穣作用を回収する。 -/
lemma leftFibrationHomTestFamily_evaluate {B : SSet.{u}} (r : LeftFibrationObject B) :
    leftFibrationHomTestFamily B ≫ evaluateFunctorAt (coherentNerveVertex r) =
      coherentNerveMap
        (relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) r) :=
  simplicialOverTestFamily_evaluate (leftFibrationOverEnriched B) r

/-- 固定標的の豊穣作用は、相対射の族による実際の前合成の同時評価。 -/
lemma relativeHomSourceEvaluationEnriched_map {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    uncurry ((relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) r).map
      (Opposite.op q) (Opposite.op a)) =
    (β_ (relativeFunctorSpace r.val.hom q.val.hom)
      (relativeFunctorSpace q.val.hom a.val.hom)).hom ≫
        relativeFunctorComposition a.val q.val r.val := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨g, f⟩
  change (relativeFunctorComposition a.val r.val r.val).app n
    ((relativeFunctorComposition a.val q.val r.val).app n (f, g),
      (relativeFunctorIdentity r.val).app n PUnit.unit) =
        (relativeFunctorComposition a.val q.val r.val).app n (f, g)
  exact congrArg (fun k ↦ k.app n
    ((relativeFunctorComposition a.val q.val r.val).app n (f, g)))
      (relativeFunctorComposition_id a.val r.val)

end SerrePositivity.InfinityCategories
