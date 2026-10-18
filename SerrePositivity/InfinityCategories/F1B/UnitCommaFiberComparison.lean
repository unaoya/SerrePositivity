module

public import SerrePositivity.InfinityCategories.F1B.UnitCommaCompositionPaths
public import SerrePositivity.InfinityCategories.F1B.HomotopyPathReplacement
public import SerrePositivity.InfinityCategories.F1B.UnitCommaLocalCriterion

/-!
概要：comma の区間写像空間から標準単位比較の導来 fiber への射を構成する。
方針：普遍正方形の合成を表すホモトピーを可逆 path の族にして、指定頂点の fiber に持ち上げる。
規約：この射の逆射や同値性はまだ主張しない。
使われ方：Kerodon §6.2.6 の局所存在判定の写像空間比較の順方向。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：comma の普遍正方形の標的が標準単位比較で固定右辺へ移るホモトピー。
方針：元の普遍正方形の上下の二単体を二辺固定で比較し、得た二経路を合成する。
規約：元の単位 η と右辺の頂点 w を固定する。
使われ方：導来 fiber への比較射の可逆 path 成分。 -/
noncomputable def unitCommaMappingComparisonHomotopy {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    SSet.Homotopy
      (unitCommaSquareTargetFamily η x w (unitCommaFiberMappingSquare
        (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w))) ≫
          unitIntervalMap η x (unitCommaFiberTargetVertex G x w))
      (SSet.const (unitCommaArrowVertex G x w)) := by
  simpa only [unitCommaArrowFamily_eq_const] using
    (unitCommaCoherentComparisonHomotopy η x w
      (unitCommaFiberMappingSquare (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w))))

/-- 概要：comma の区間写像空間から標準単位比較の導来 fiber への実際の射。
方針：普遍正方形の標的とホモトピーで path 置換へ写し、右辺の固定頂点の fiber に入れる。
規約：比較射が同値であるという追加仮定を置かず、ここでは同値性を結論しない。
使われ方：局所存在判定で可縮性を移すための比較射の順方向。 -/
noncomputable def unitCommaMappingToComparisonFiber {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    intervalMappingSpace (unitCommaSectionVertex η x) w ⟶
      unitIntervalComparisonFiber η x (unitCommaFiberTargetVertex G x w)
        (unitCommaArrowVertex G x w) :=
  vertexFiberLift (equivalencePathReplacementMap
      (unitIntervalMap η x (unitCommaFiberTargetVertex G x w))) (unitCommaArrowVertex G x w)
    (homotopyPathReplacementLift _ _ (unitCommaMappingComparisonHomotopy η x w))
    (homotopyPathReplacementLift_map _ _ (unitCommaMappingComparisonHomotopy η x w))

/-- 概要：導来 fiber への比較射の元の始域への射影は正方形の標的族。
方針：fiber の持ち上げと path 置換の第二射影の公式を使う。
規約：始域は F(x) から w の標的への区間写像空間。
使われ方：比較射が正しい単位比較の底の上にあることの検証。 -/
lemma unitCommaMappingToComparisonFiber_projection {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    unitCommaMappingToComparisonFiber η x w ≫
      vertexFiberι (equivalencePathReplacementMap
        (unitIntervalMap η x (unitCommaFiberTargetVertex G x w))) (unitCommaArrowVertex G x w) ≫
      equivalencePathReplacementProjection
        (unitIntervalMap η x (unitCommaFiberTargetVertex G x w)) =
        unitCommaSquareTargetFamily η x w (unitCommaFiberMappingSquare
          (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w))) := by
  rw [← Category.assoc]
  change (vertexFiberLift _ _ _ _ ≫ vertexFiberι _ _) ≫ _ = _
  rw [vertexFiberLift_ι, homotopyPathReplacementLift_projection]

end SerrePositivity.InfinityCategories
