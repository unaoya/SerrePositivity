module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalIndexPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftPullbackHomotopyPrism

/-!
概要：指定添字ホモトピーを右Kan局所形状の射と元の標準錐の全prismへ移す。
方針：同じcoslice射影への引き戻しprismを、固定頂点の錐の境界法則に代入する。
規約：HTT 5.1.5.6、Kerodon Tag 02Y9の既存局所錐の計算法則。
  形状の射の同値性と分類像の一致は、ここではまだ主張しない。
使われ方：R04の指定余単位との合成に、同じ元の添字ホモトピーを残す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 同じ指定添字ホモトピーは、局所射影と頂点を保つ元の標準錐のprismを与える。 -/
@[cite HTT "5.1.5.6" (partial := special) "右Kanの同じcoslice上の標準錐の境界法則。"]
lemma exists_rightKanIndexShapePrism {K C D : SSet.{u}} [Quasicategory C]
    {f g : K ⟶ C} (α : SSet.Homotopy f g) (G : C ⟶ D) (v : C _⦋0⦌) :
    ∃ (a : rightKanShape f v ⟶ rightKanShape g v)
      (Q : join (Δ[0] : SSet.{u}) (rightKanShape f v) ⊗ (Δ[1] : SSet.{u}) ⟶ D),
      a ≫ rightKanProjection g v = rightKanProjection f v ∧
      SSet.ι₀ ≫ Q = (rightKanCanonicalCone f G v).val ∧
      SSet.ι₁ ≫ Q = joinMap (𝟙 (Δ[0] : SSet.{u})) a ≫
        (rightKanCanonicalCone g G v).val ∧
      (joinInr (Δ[0] : SSet.{u}) (rightKanShape f v) ▷ (Δ[1] : SSet.{u})) ≫ Q =
        (rightKanProjection f v ▷ (Δ[1] : SSet.{u})) ≫ α.h ≫ G ∧
      (joinInl (Δ[0] : SSet.{u}) (rightKanShape f v) ▷ (Δ[1] : SSet.{u})) ≫ Q =
        fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm v ≫ G := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm v)
  obtain ⟨a, H, ha, hH⟩ := exists_leftPullbackHomotopyPrism p α
  obtain ⟨Q, h₀, h₁, hd, hv⟩ := exists_cosliceHomotopyConePrism v H G
  refine ⟨a, Q, ha, h₀, ?_, ?_, hv⟩
  · rw [h₁, sliceUnderUncurry_precomp, Category.assoc]
    rfl
  · rw [← Category.assoc H.h, hH, Category.assoc] at hd
    exact hd

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
