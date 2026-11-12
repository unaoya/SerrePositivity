module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSlicePostcompIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceOverEqualityTransport

/-!
概要：right fibration の写像空間の span を、同じ底上の射に沿って比較する。
方針：終点を正規化した slice 後合成を頂点 fiber に制限し、全族の持ち上げを比較する。
規約：選択した切断そのものの厳密な自然性は要求しない。
使われ方：Kerodon §7.4 の表現可能比較、G8 の固定端点錐の族の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：終点を正規化した slice 後合成は、実関手の合成を保つ。
方針：全錐を uncurry し、既存の後合成の公式で比較する。
規約：fibration 性を仮定しない。使われ方：比較 span の射影の合成則。 -/
lemma pointSlicePostcomp_comp {E F B : SSet.{u}} (f : E ⟶ F) (s : F ⟶ B)
    (c : E _⦋0⦌) :
    pointSlicePostcomp f c ≫ pointSlicePostcomp s (f.app _ c) =
      pointSlicePostcomp (f ≫ s) c := by
  apply sliceOverUncurry_injective
  rw [pointSlicePostcomp_uncurry]
  have hf := pointSlicePostcomp_uncurry f c (𝟙 _)
  have hfs := pointSlicePostcomp_uncurry (f ≫ s) c (𝟙 _)
  simp only [Category.id_comp] at hf hfs
  rw [hf, hfs, Category.assoc]

/-- 概要：同じ底上の実射が、終点を正規化した比較 span の全空間に誘導する射。
方針：slice の後合成を、同じ底の頂点で fiber に制限する。
規約：底への射を f≫s と書き、底の終点の同定を定義的に保つ。
使われ方：選択した切断の全族の比較。 -/
def rightFibrationMappingOverMap {E F B : SSet.{u}} (f : E ⟶ F) (s : F ⟶ B)
    (c : E _⦋0⦌) (x : B _⦋0⦌) :
    rightFibrationMappingTotal (f ≫ s) c x ⟶
      rightFibrationMappingTotal s (f.app _ c) x :=
  vertexFiberMap (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ (f ≫ s))
    (sliceOverProjection (SSet.yonedaEquiv.symm (f.app _ c)) ≫ s)
    (pointSlicePostcomp f c) (by
      rw [← Category.assoc, pointSlicePostcomp_projection, Category.assoc]) x

/-- 比較 span の誘導射を全空間へ含めると、元の slice 後合成になる。 -/
lemma rightFibrationMappingOverMap_ι {E F B : SSet.{u}} (f : E ⟶ F) (s : F ⟶ B)
    (c : E _⦋0⦌) (x : B _⦋0⦌) :
    rightFibrationMappingOverMap f s c x ≫
        vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm (f.app _ c)) ≫ s) x =
      vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ (f ≫ s)) x ≫
        pointSlicePostcomp f c :=
  vertexFiberMap_ι _ _ _ _ _

/-- 概要：比較 span の底上の射は、始点評価と厳密に可換。
方針：fiber の包含後に、正規化した slice 後合成の射影の式を使う。
規約：全パラメータでの射の等式。使われ方：全族の切断比較後の評価。 -/
lemma rightFibrationMappingOverMap_evaluation {E F B : SSet.{u}}
    (f : E ⟶ F) (s : F ⟶ B) (c : E _⦋0⦌) (x : B _⦋0⦌) :
    rightFibrationMappingOverMap f s c x ≫
        rightFibrationMappingEvaluation s (f.app _ c) x =
      rightFibrationMappingEvaluation (f ≫ s) c x ≫
        vertexFiberMap (f ≫ s) s f rfl x := by
  apply vertexFiber_hom_ext s x
  simp only [Category.assoc, rightFibrationMappingEvaluation, vertexFiberMap_ι]
  rw [← Category.assoc, rightFibrationMappingOverMap_ι, Category.assoc,
    pointSlicePostcomp_projection]
  rfl

/-- 図式の等式による slice の頂点 fiber の輸送は、包含後には slice の輸送そのもの。
等式を消去して示し、比較 span の終点の正規化に使う。 -/
lemma sliceOverVertexFiber_transport_ι {K B : SSet.{u}} {p q : K ⟶ B}
    (h : p = q) (x : B _⦋0⦌) :
    (eqToIso (congrArg (fun t => vertexFiber (sliceOverProjection t) x) h)).hom ≫
        vertexFiberι (sliceOverProjection q) x =
      vertexFiberι (sliceOverProjection p) x ≫ (eqToIso (congrArg sliceOver h)).hom := by
  subst h
  simp

/-- 概要：元の pinched Hom への射影を slice の fiber へ戻すと、正規化した後合成になる。
方針：既存の射影の定義と等式による fiber の包含の移送を比較する。
規約：選択した切断を変えない。使われ方：同じ底上の射での span の射影の自然性。 -/
lemma rightFibrationMappingHomProjection_normalized_ι {E B : SSet.{u}}
    (r : E ⟶ B) (c : E _⦋0⦌) (x : B _⦋0⦌) :
    rightFibrationMappingHomProjection r c x ≫
        (pinchedHomSliceFiberIso x (r.app _ c)).hom ≫
        vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm (r.app _ c))) x =
      vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) x ≫
        pointSlicePostcomp r c := by
  dsimp only [rightFibrationMappingHomProjection, rightFibrationMappingBaseIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [sliceOverVertexFiber_transport_ι (SSet.yonedaEquiv_symm_comp c r) x,
    pointSlicePostcomp_eq_postcomp_transport]
  rw [← Category.assoc, rightFibrationMappingProjection, vertexFiberMap_ι,
    Category.assoc]
  rfl

/-- 概要：比較 span の底上の射は、元の pinched Hom への射影と厳密に可換。
方針：pinched Hom を正規化した slice の fiber に戻し、後合成の合成則を使う。
規約：終点は f≫s の像そのもの。使われ方：共通の自明 Kan fibration 上の切断比較。 -/
lemma rightFibrationMappingOverMap_projection {E F B : SSet.{u}}
    (f : E ⟶ F) (s : F ⟶ B) (c : E _⦋0⦌) (x : B _⦋0⦌) :
    rightFibrationMappingOverMap f s c x ≫
        rightFibrationMappingHomProjection s (f.app _ c) x =
      rightFibrationMappingHomProjection (f ≫ s) c x := by
  apply (cancel_mono (pinchedHomSliceFiberIso x ((f ≫ s).app _ c)).hom).mp
  apply vertexFiber_hom_ext
    (sliceOverProjection (SSet.yonedaEquiv.symm ((f ≫ s).app _ c))) x
  simp only [Category.assoc]
  rw [rightFibrationMappingHomProjection_normalized_ι (f ≫ s) c x]
  simp only [NatTrans.comp_app, types_comp_apply]
  rw [rightFibrationMappingHomProjection_normalized_ι s (f.app _ c) x]
  rw [← Category.assoc, rightFibrationMappingOverMap_ι, Category.assoc,
    pointSlicePostcomp_comp]

/-- 概要：同じ底上の射に沿う right fibration の表現可能比較は、全族の関手同型で可換。
方針：標的側の共通の自明 Kan fibration 上で二つの切断を比較し、始点へ評価する。
規約：既存の選択した切断を使用し、その厳密な自然性を追加仮定しない。
使われ方：固定端点錐の族への移送と G8 の切断制限の比較。 -/
def rightFibrationHomComparison_overMapIso {E F B : SSet.{u}}
    (f : E ⟶ F) (s : F ⟶ B) [RightFibration (f ≫ s)] [RightFibration s]
    (c : E _⦋0⦌) (x : B _⦋0⦌) :
    FunctorIso
      (rightFibrationHomComparison (f ≫ s) c x ≫ vertexFiberMap (f ≫ s) s f rfl x)
      (rightFibrationHomComparison s (f.app _ c) x) := by
  let H := functorIsoOfTrivialKanFibration
    (rightFibrationMappingHomProjection s (f.app _ c) x)
    (rightFibrationMappingSection (f ≫ s) c x ≫ rightFibrationMappingOverMap f s c x)
    (rightFibrationMappingSection s (f.app _ c) x) (by
      rw [Category.assoc, rightFibrationMappingOverMap_projection,
        rightFibrationMappingSection_projection, rightFibrationMappingSection_projection]
      rfl)
  simpa only [rightFibrationHomComparison, Category.assoc,
    rightFibrationMappingOverMap_evaluation] using
    H.postcomp (rightFibrationMappingEvaluation s (f.app _ c) x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
