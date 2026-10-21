module

public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalOuterHornGluing
public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalHomSquareCurry

/-!
概要：外ホーン上で整合する同じ二三角形から、元の固定成分 Hom fiber の族を構成する。
方針：三辺固定の標準正方形を同じ fiber に curry し、両三角形の制限を回収する。
規約：元の第一・第二三角形と全パラメーターを保持する。
使われ方：外ホーン延長を表す実際の pullback の存在証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (vertexFiber (cocartesianHomIntervalEvaluation F G c) v)
variable {T : SSet.{u + 1}}
  (a : T ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj CatInfinity.{u})
  (b : T ⟶ cocartesianIntervalCompositionSpace F G v)
  (h : a ≫ ((pre (horn 2 2).ι).app CatInfinity.{u}) =
    b ≫ cocartesianIntervalOuterHornMap F G v)

/-- 元の外ホーン上で整合する二三角形を、実際の固定成分 Hom fiber の同じ族へ戻す。 -/
def cocartesianIntervalOuterHornLift : T ⟶ E :=
  cocartesianIntervalHomSquareCurry F G v (cocartesianIntervalOuterHornComparisonSquare F G v a b h)
    (cocartesianIntervalOuterHornComparisonSquare_zero F G v a b h)
    (cocartesianIntervalOuterHornComparisonSquare_one F G v a b h)
    (cocartesianIntervalOuterHornComparisonSquare_at_one F G v a b h)

/-- 同じ持ち上げを標準正方形に戻すと、元の二三角形の貼り合わせそのもの。 -/
lemma cocartesianIntervalOuterHornLift_square :
    cocartesianIntervalHomSquare F G v (cocartesianIntervalOuterHornLift F G v a b h) =
      cocartesianIntervalOuterHornComparisonSquare F G v a b h :=
  cocartesianIntervalHomSquare_curry F G v _ _ _ _

/-- 同じ持ち上げの第一三角形は、元の第一三角形の族を厳密に回収する。 -/
lemma cocartesianIntervalOuterHornLift_first :
    cocartesianIntervalHomTriangle F G v 0 (cocartesianIntervalOuterHornLift F G v a b h) =
      innerTriangleExtensionUncurry b := by
  unfold cocartesianIntervalHomTriangle
  rw [cocartesianIntervalOuterHornLift_square, cocartesianIntervalOuterHornComparisonSquare_first]

/-- 同じ持ち上げの第二三角形は、元の第二三角形の族を厳密に回収する。 -/
lemma cocartesianIntervalOuterHornLift_second :
    cocartesianIntervalHomTriangle F G v 1 (cocartesianIntervalOuterHornLift F G v a b h) =
      uncurry a := by
  unfold cocartesianIntervalHomTriangle
  rw [cocartesianIntervalOuterHornLift_square, cocartesianIntervalOuterHornComparisonSquare_second]

/-- 同じ持ち上げの第二三角形への実際の射影は、元の全内部 Hom の族を回収する。 -/
lemma cocartesianIntervalOuterHornLift_fst :
    cocartesianIntervalOuterHornLift F G v a b h ≫
      cocartesianIntervalSecondTriangleMap F G v = a := by
  apply uncurry_injective
  rw [cocartesianIntervalSecondTriangleMap_uncurry, cocartesianIntervalOuterHornLift_second]

/-- 同じ持ち上げの合成三角形への実際の射影は、元の全族を回収する。 -/
lemma cocartesianIntervalOuterHornLift_snd :
    cocartesianIntervalOuterHornLift F G v a b h ≫
      cocartesianIntervalCompositionTriangleMap F G v = b := by
  apply innerTriangleExtensionUncurry_injective _
  rw [cocartesianIntervalCompositionTriangleMap_uncurry, cocartesianIntervalOuterHornLift_first]

end SerrePositivity.InfinityCategories
