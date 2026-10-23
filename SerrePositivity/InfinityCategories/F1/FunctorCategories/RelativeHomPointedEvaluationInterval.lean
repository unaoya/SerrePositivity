module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomPointedRecoveryPrism
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostcompositionVertices

/-!
概要：pointed 回収の底の区間族を、元の coherent 評価の同じ右 Hom で表す。
方針：pinched 模型の端点表示変更を区間模型へ移し、標準 Kan 頂点で正規化する。
規約：元の relativeHomCoherentEvaluationMap と全パラメーターを保つ。
使われ方：同じ pointed 輸送を、元の coherent Hom 比較の逆による回収へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- pinched Hom の端点表示変更は、同じ区間族の端点表示変更そのもの。 -/
lemma pinchedHomToIntervalMappingSpace_vertices {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    eqToHom (congrArg₂ (fun a b ↦ pinchedHom a b) hx hy) ≫
      pinchedHomToIntervalMappingSpace x' y' =
      pinchedHomToIntervalMappingSpace x y ≫ intervalMappingPostOfEq (𝟙 X) x y hx hy := by
  subst x'
  subst y'
  apply intervalMappingUncurry_injective x y
  rw [eqToHom_refl, Category.id_comp, intervalMappingPostOfEq_uncurry, Category.comp_id]

/-- 端点を表示変更して区間へ展開しても、元の全パラメーターの区間族は変わらない。 -/
lemma pinchedHomToIntervalMappingSpace_vertices_uncurry
    {X T : SSet.{u}} {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y')
    (f : T ⟶ pinchedHom x y) :
    intervalMappingUncurry ((f ≫ eqToHom (congrArg₂ (fun a b ↦ pinchedHom a b) hx hy)) ≫
      pinchedHomToIntervalMappingSpace x' y') =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y) := by
  rw [Category.assoc, pinchedHomToIntervalMappingSpace_vertices hx hy, ← Category.assoc,
    intervalMappingPostOfEq_uncurry, Category.comp_id]

/-- 元の coherent 評価を、同じ標準 Kan 頂点間の区間族として表す。 -/
def relativeHomPointedEvaluationInterval {B : SSet.{u}} (a q : LeftFibrationObject B) :
    pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val)) ⟶
        intervalMappingSpace
          (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj q))
          (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation a.val).obj q)) :=
  (relativeHomCoherentEvaluationMap a q q ≫ pinchedHomToIntervalMappingSpace _ _) ≫
    intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
      (coherentNerveVertex ((relativeFunctorEnrichedEvaluation q.val).obj q))
      (coherentNerveVertex ((relativeFunctorEnrichedEvaluation a.val).obj q))
      (spaceInfinityVertex_eq_coherent ((relativeFunctorEnrichedEvaluation q.val).obj q)).symm
      (spaceInfinityVertex_eq_coherent ((relativeFunctorEnrichedEvaluation a.val).obj q)).symm

/-- 正規化した区間族の展開は、元の coherent 変換を同じ表現対象で評価した族。 -/
lemma relativeHomPointedEvaluationInterval_uncurry {B : SSet.{u}}
    (a q : LeftFibrationObject B) :
    intervalMappingUncurry (relativeHomPointedEvaluationInterval a q) =
      lift (fst (Δ[1] : SSet.{u + 1}) _)
        (lift (SSet.const (coherentNerveVertex q)) (snd (Δ[1] : SSet.{u + 1}) _)) ≫
          relativeHomCoherentTransformationPrism a q := by
  let X := (relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) q).obj
    (Opposite.op q)
  let Y := (relativeHomSourceEvaluationEnriched (leftFibrationOverEnriched B) q).obj
    (Opposite.op a)
  have h := intervalMappingPostOfEq_uncurry (𝟙 SpaceInfinity.{u})
    (coherentNerveVertex X) (coherentNerveVertex Y)
    (spaceInfinityVertex_eq_coherent X).symm (spaceInfinityVertex_eq_coherent Y).symm
    (relativeHomCoherentEvaluationMap a q q ≫ pinchedHomToIntervalMappingSpace _ _)
  calc
    _ = intervalMappingUncurry
        (relativeHomCoherentEvaluationMap a q q ≫ pinchedHomToIntervalMappingSpace _ _) :=
      h.trans (Category.comp_id _)
    _ = intervalMappingUncurry
        (pinchedHomMap (evaluateFunctorAt (coherentNerveVertex q))
          (functorVertex (leftFibrationCoherentEvaluation q.val))
          (functorVertex (leftFibrationCoherentEvaluation a.val)) ≫
          pinchedHomToIntervalMappingSpace _ _) :=
      pinchedHomToIntervalMappingSpace_vertices_uncurry
        (relativeHomCoherentEvaluation_vertex q q) (relativeHomCoherentEvaluation_vertex a q) _
    _ = _ := (relativeHomCoherentTransformationPrism_evaluate a q q).symm

end SerrePositivity.InfinityCategories
