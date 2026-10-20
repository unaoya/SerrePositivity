module

public import SerrePositivity.InfinityCategories.F1.FunctorNaturalityTriangles
public import SerrePositivity.InfinityCategories.F1.CosliceIntervalNaturality
public import SerrePositivity.InfinityCategories.F1.RelativeHomCoherentRecovery

/-!
概要：任意の coherent な Hom 関手間の変換の自然性を、全相対射の族で同時に表す。
方針：変換空間の普遍 prism と、相対 Hom の普遍 prism を合成して四角形を作る。
規約：変換と射のパラメーターを頂点へ制限せず、四辺の厳密な端点を保つ。
使われ方：恒等射で回収した変換を元の coherent 変換へ戻す往復の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 全 coherent 変換を、元の底と変換のパラメーターを保つ普遍 prism へ展開する。 -/
def relativeHomCoherentTransformationPrism {B : SSet.{u}} (a q : LeftFibrationObject B) :
    (Δ[1] : SSet.{u + 1}) ⊗ (LeftFibrationInfinity B ⊗
      pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val))) ⟶ SpaceInfinity.{u} :=
  coherentTransformationFamilyDiagram (pinchedHomToIntervalMappingSpace
    (functorVertex (leftFibrationCoherentEvaluation q.val))
    (functorVertex (leftFibrationCoherentEvaluation a.val)))

/-- 普遍変換の零端は、変換のパラメーターに定値な元の Hom 関手。 -/
lemma relativeHomCoherentTransformationPrism_zero {B : SSet.{u}} (a q : LeftFibrationObject B) :
    prismEndpoint 0 _ ≫ relativeHomCoherentTransformationPrism a q =
      fst _ _ ≫ leftFibrationCoherentEvaluation q.val :=
  coherentTransformationFamilyDiagram_zero _

/-- 普遍変換の一端は、同じパラメーターに定値な終域の Hom 関手。 -/
lemma relativeHomCoherentTransformationPrism_one {B : SSet.{u}} (a q : LeftFibrationObject B) :
    prismEndpoint 1 _ ≫ relativeHomCoherentTransformationPrism a q =
      fst _ _ ≫ leftFibrationCoherentEvaluation a.val :=
  coherentTransformationFamilyDiagram_one _


/-- 普遍変換のテスト標的での制限は、実際の pinchedHomMap の区間への展開。 -/
lemma relativeHomCoherentTransformationPrism_evaluate {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    lift (fst (Δ[1] : SSet.{u + 1}) _)
      (lift (SSet.const (coherentNerveVertex r)) (snd (Δ[1] : SSet.{u + 1}) _)) ≫
        relativeHomCoherentTransformationPrism a q =
    intervalMappingUncurry
      (pinchedHomMap (evaluateFunctorAt (coherentNerveVertex r))
        (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val)) ≫
          pinchedHomToIntervalMappingSpace _ _) := by
  rw [pinchedHomToIntervalMappingSpace_naturality, intervalFunctorMap_uncurry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  rfl

/-- 全相対射を、その始域と標的を固定した coherent な射の prism へ展開する。 -/
def relativeHomArrowPrism {B : SSet.{u}} (q r : LeftFibrationObject B) :
    (Δ[1] : SSet.{u + 1}) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace r.val.hom q.val.hom) ⟶
        LeftFibrationInfinity B :=
  intervalMappingUncurry (coherentHomComparison q r ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex q) (coherentNerveVertex r))

/-- 全相対射の prism の始点は指定した始域の標準頂点。 -/
lemma relativeHomArrowPrism_zero {B : SSet.{u}} (q r : LeftFibrationObject B) :
    prismEndpoint 0 _ ≫ relativeHomArrowPrism q r = SSet.const (coherentNerveVertex q) :=
  intervalMappingUncurry_zero _

/-- 全相対射の prism の終点は指定した標的の標準頂点。 -/
lemma relativeHomArrowPrism_one {B : SSet.{u}} (q r : LeftFibrationObject B) :
    prismEndpoint 1 _ ≫ relativeHomArrowPrism q r = SSet.const (coherentNerveVertex r) :=
  intervalMappingUncurry_one _

/-- 変換と相対射の両パラメーターを同時に保つ、実際の coherent 自然性の四角形。 -/
def relativeHomCoherentNaturalitySquare {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[1] ⊗
      ((SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace r.val.hom q.val.hom) ⊗
        pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
          (functorVertex (leftFibrationCoherentEvaluation a.val)))) ⟶ SpaceInfinity.{u} :=
  functorNaturalitySquare (relativeHomCoherentTransformationPrism a q) (relativeHomArrowPrism q r)

/-- 変換の零端での辺は、元の Hom 関手による全相対射の作用。 -/
lemma relativeHomCoherentNaturalitySquare_transformation_zero {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    prismEndpoint 0 _ ≫ relativeHomCoherentNaturalitySquare a q r =
      (Δ[1] ◁ fst _ _) ≫ relativeHomArrowPrism q r ≫ leftFibrationCoherentEvaluation q.val :=
  functorNaturalitySquare_transformationFace _ _ 0 _
    (relativeHomCoherentTransformationPrism_zero a q)

/-- 変換の一端での辺は、終域の Hom 関手による同じ全相対射の作用。 -/
lemma relativeHomCoherentNaturalitySquare_transformation_one {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    prismEndpoint 1 _ ≫ relativeHomCoherentNaturalitySquare a q r =
      (Δ[1] ◁ fst _ _) ≫ relativeHomArrowPrism q r ≫ leftFibrationCoherentEvaluation a.val :=
  functorNaturalitySquare_transformationFace _ _ 1 _
    (relativeHomCoherentTransformationPrism_one a q)

/-- 相対射の始点での辺は、表現対象での元の普遍変換の評価。 -/
lemma relativeHomCoherentNaturalitySquare_arrow_zero {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    (Δ[1] ◁ prismEndpoint 0 _) ≫ relativeHomCoherentNaturalitySquare a q r =
      lift (fst (Δ[1] : SSet.{u + 1}) _)
        (lift (SSet.const (coherentNerveVertex q))
          (snd (Δ[1] : SSet.{u + 1}) _ ≫ snd _ _)) ≫
            relativeHomCoherentTransformationPrism a q :=
  functorNaturalitySquare_arrowFace _ _ 0 _ (relativeHomArrowPrism_zero q r)

/-- 相対射の終点での辺は、各テスト標的での元の普遍変換の評価。 -/
lemma relativeHomCoherentNaturalitySquare_arrow_one {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    (Δ[1] ◁ prismEndpoint 1 _) ≫ relativeHomCoherentNaturalitySquare a q r =
      lift (fst (Δ[1] : SSet.{u + 1}) _)
        (lift (SSet.const (coherentNerveVertex r))
          (snd (Δ[1] : SSet.{u + 1}) _ ≫ snd _ _)) ≫
            relativeHomCoherentTransformationPrism a q :=
  functorNaturalitySquare_arrowFace _ _ 1 _ (relativeHomArrowPrism_one q r)


/-- 自然性の始点側の縦辺は、表現対象での実際の coherent な評価の全パラメーター族。 -/
lemma relativeHomCoherentNaturalitySquare_evaluation_zero {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    (Δ[1] ◁ prismEndpoint 0 _) ≫ relativeHomCoherentNaturalitySquare a q r =
      (Δ[1] ◁ snd _ _) ≫ intervalMappingUncurry
        (pinchedHomMap (evaluateFunctorAt (coherentNerveVertex q))
          (functorVertex (leftFibrationCoherentEvaluation q.val))
          (functorVertex (leftFibrationCoherentEvaluation a.val)) ≫
            pinchedHomToIntervalMappingSpace _ _) := by
  rw [relativeHomCoherentNaturalitySquare_arrow_zero,
    ← relativeHomCoherentTransformationPrism_evaluate]
  rfl

/-- 自然性の終点側の縦辺は、各標的での実際の coherent な評価の全パラメーター族。 -/
lemma relativeHomCoherentNaturalitySquare_evaluation_one {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    (Δ[1] ◁ prismEndpoint 1 _) ≫ relativeHomCoherentNaturalitySquare a q r =
      (Δ[1] ◁ snd _ _) ≫ intervalMappingUncurry
        (pinchedHomMap (evaluateFunctorAt (coherentNerveVertex r))
          (functorVertex (leftFibrationCoherentEvaluation q.val))
          (functorVertex (leftFibrationCoherentEvaluation a.val)) ≫
            pinchedHomToIntervalMappingSpace _ _) := by
  rw [relativeHomCoherentNaturalitySquare_arrow_one,
    ← relativeHomCoherentTransformationPrism_evaluate]
  rfl

/-- 自然性の二つの合成順序を、元の四角形から三角形の族として取り出す。 -/
def relativeHomCoherentNaturalityTriangle {B : SSet.{u}} (a q r : LeftFibrationObject B)
    (i : Fin 2) :=
  squarePrismTriangle (relativeHomCoherentNaturalitySquare a q r) i

/-- 両合成順序の長辺は、両パラメーターの全体で厳密に一致する。 -/
lemma relativeHomCoherentNaturalityTriangle_longEdge {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ relativeHomCoherentNaturalityTriangle a q r 0 =
      (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ relativeHomCoherentNaturalityTriangle a q r 1 := by
  rw [relativeHomCoherentNaturalityTriangle, relativeHomCoherentNaturalityTriangle,
    squarePrismTriangle_diagonal, squarePrismTriangle_diagonal]

end SerrePositivity.InfinityCategories
