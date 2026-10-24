module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaSquareComparisonPath
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyPathReplacement
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaLocalCriterion

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
方針：元の普遍正方形全体への三辺固定の比較から右辺の経路を取り出す。
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
  let H := unitCommaSquareComparisonHomotopy η x w
    (unitCommaFiberMappingSquare (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w)))
  exact { h := H.h
          h₀ := H.h₀
          h₁ := H.h₁.trans (unitCommaArrowFamily_eq_const G x w _)
          rel := H.rel }

/-- 概要：順方向比較の path の正方形表示は普遍正方形の全体比較の右辺そのもの。
方針：終点を定値族と認識しても raw なホモトピーが変わらないことを使う。
規約：実際の図式の厳密な一致。
使われ方：順方向比較と復元側の境界輸送の照合。 -/
lemma unitCommaMappingComparisonHomotopy_square {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    intervalFamilySquare (unitCommaMappingComparisonHomotopy η x w) =
      (unitCommaSquareComparison η x w (unitCommaFiberMappingSquare
        (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w)))).rightSquare :=
  unitCommaSquareComparisonHomotopy_square _ _ _ _

/-- 概要：順方向比較の可逆 path は普遍正方形の全体 path の右辺そのもの。
方針：終点の定値化が raw なホモトピーを変えないことと、右辺の path の公式を使う。
規約：実際の可逆 path の厳密な一致。
使われ方：復元側の指定境界輸送との比較の普遍族上の式。 -/
lemma unitCommaMappingComparisonHomotopy_path {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ unitCommaSquareComparisonPath η x w
      (unitCommaFiberMappingSquare (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w))) =
        intervalFamilyPath (unitCommaMappingComparisonHomotopy η x w) :=
  unitCommaSquareComparisonPath_right _ _ _ _

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
