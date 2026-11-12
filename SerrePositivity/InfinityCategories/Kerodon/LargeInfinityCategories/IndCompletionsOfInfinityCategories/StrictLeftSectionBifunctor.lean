module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictLeftClassificationSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalRelativeConstant
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：底の全相対図式と元の strict left fibration 図式を同時に動かす Kan 値二変数関手。
方針：相対前合成と後合成の可換性を使い、一つの通常の図式値関手を uncurry する。
規約：両変数の恒等・合成を厳密に保ち、頂点ごとの選択をしない。
使われ方：全単体の切断の replacement から共同 weighted 全空間への大域比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ底上の射による後合成と、任意の底上の図式の前合成は可換。 -/
lemma relativeFunctorPost_overPre {B X Y : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y) (hf : f ≫ q = p)
    {a b : Over B} (r : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf b.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q r =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf a.hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (ihom b.left).map f) ≫ (pre r.left).app Y =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (pre r.left).app X) ≫ (ihom a.left).map f
  rw [Category.assoc, Category.assoc, (pre r.left).naturality f]

variable {I J : Type u} [Category.{u} I] [Category.{u} J] {B : SSet.{u}}
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (A : Jᵒᵖ ⥤ Over B)

/-- 元の図式の同じ射は、全ての相対定義域上で一つの後合成自然変換を誘導する。 -/
def strictLeftSectionPost {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorKanDiagram A (F.obj i) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorKanDiagram A (F.obj j) where
  app s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (F.obj i).val.hom (F.obj j).val.hom
    (F.map f).left (Over.w (F.map f)) (A.obj (Opposite.op s)).hom
  naturality s t g := (relativeFunctorPost_overPre (F.obj i).val.hom (F.obj j).val.hom
    (F.map f).left (Over.w (F.map f)) (A.map g.op)).symm

/-- 両変数の元の射の作用を同時に保持する、Kan 図式値の通常の関手。 -/
def strictLeftSectionCurried : I ⥤ J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorKanDiagram A (F.obj i)
  map := strictLeftSectionPost F A
  map_id i := by
    apply NatTrans.ext
    funext s
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (F.obj i).val.hom (F.obj i).val.hom
      (F.map (𝟙 i)).left (Over.w (F.map (𝟙 i))) (A.obj (Opposite.op s)).hom = 𝟙 _
    rw [F.map_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPost_id _ _
  map_comp {i j k} f g := by
    apply NatTrans.ext
    funext s
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (F.obj i).val.hom (F.obj k).val.hom
      (F.map (f ≫ g)).left (Over.w (F.map (f ≫ g))) (A.obj (Opposite.op s)).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (F.obj i).val.hom (F.obj j).val.hom
        (F.map f).left (Over.w (F.map f)) (A.obj (Opposite.op s)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (F.obj j).val.hom (F.obj k).val.hom
        (F.map g).left (Over.w (F.map g)) (A.obj (Opposite.op s)).hom
    rw [F.map_comp]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPost_comp _ _ _ _ _ _ _ _).symm

/-- 同じ二変数関手を積の添字の一つの Kan 値図式として読む。 -/
def strictLeftSectionProductDiagram : I × J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  CategoryTheory.Functor.uncurry.obj (strictLeftSectionCurried F A)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
