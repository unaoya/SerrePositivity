module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChangePullbackData
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveStraighteningRepresentation

/-!
概要：同じ初頂点四角形の二経路のnative制限の合成則。
方針：既存の表現の外延性と指定pullbackの二座標を使う。
規約：HTT §3.3.2・Kerodon Tag 028Tの構成の特殊化。別の制限は選ばない。
使われ方：P3-Dの係数の端点を元のnative制限へ揃える。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 初頂点の四角形に沿う二つのnative制限は、元の同じ表現のデータとして一致する。
HTT §3.3.2・Kerodon Tag 028Tの構成の、この指定四角形での合成則。 -/
@[cite HTT "3.3.2" (partial := special) "指定初頂点四角形に沿うnative表現制限の合成則。"]
lemma nativeRestrict_firstVertex_diamond
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let d := leftStraighteningBaseChangePullbackData p k
    (R.nativeRestrict lB).cartesianRestrict (U.map d.val) (U.map (nerveMap H))
      d.property.2.2.2 = (R.nativeRestrict k).nativeRestrict lD := by
  dsimp only
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let d := leftStraighteningBaseChangePullbackData p k
  apply LeftTransportRepresentation.ext
  · change U.map (nerveMap H) ≫ U.map lB ≫ R.diagram = U.map lD ≫ U.map k ≫ R.diagram
    rw [← Category.assoc, ← U.map_comp, transportSimplexFirstVertexMap_naturality k,
      U.map_comp, Category.assoc]
  · simp only [LeftTransportRepresentation.cartesianRestrict_pointedMap,
      LeftTransportRepresentation.nativeRestrict_pointedMap]
    change U.map d.val ≫ U.map (pullback.fst p lB) ≫ R.pointedMap =
      U.map (pullback.fst q lD) ≫ U.map (pullback.fst p k) ≫ R.pointedMap
    rw [← Category.assoc, ← U.map_comp, d.property.1, U.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
