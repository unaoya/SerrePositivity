module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ResolutionEnrichedComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramSimplicialCategory

/-!
概要：解像への標準比較を二点の strict な Kan 値図式の豊穣的な族として表す。
方針：始点に元の Kan 複体、終点に解像を置き、豊穣自然性で変換空間の条件を満たす。
規約：二点の順序は Hom と同じ宇宙 u に持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、標準比較を図式全体の coherent な比較へ実現する入力。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：Kan 複体から解像への標準比較を二点の図式にする。
方針：一つの射からなる図式を有限順序の宇宙持ち上げに沿って引き戻す。
規約：零が元の Kan 複体、一が解像を表す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較の二つの端点を保持する strict な図式。 -/
noncomputable def coherentResolutionArrowDiagram (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    ULift.{u} (Fin 2) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
    ComposableArrows.mk₁
      (show X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionKanEnriched.obj X from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison X.obj)

/-- 概要：内部 Hom の単体から標準比較の二点の図式間の strict な変換を作る。
方針：始点では元の単体、終点では解像の豊穣作用を使い、標準比較の豊穣自然性を適用する。
規約：単体のパラメーターは全次数で同じものを使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較の図式の族の Hom の作用。 -/
noncomputable def coherentResolutionArrowMappingSimplex (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    {n : SimplexCategoryᵒᵖ} (η : ((ihom X.obj).obj Y.obj).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex (coherentResolutionArrowDiagram X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (coherentResolutionArrowDiagram Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) n := by
  refine ⟨(fun i ↦ ?_), ?_⟩
  · rcases i with ⟨i⟩
    refine Fin.cases (motive := fun j : Fin 2 ↦
      ((ihom ((coherentResolutionArrowDiagram X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj (ULift.up j))).obj
        ((coherentResolutionArrowDiagram Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj (ULift.up j))).obj n) η ?_ i
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionEnrichedMap X.obj Y.obj).app n η
  · intro i j f k α x
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j
    · rfl
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionEnrichedMap_app_comparison X.obj Y.obj η α x).symm
    · have h := leOfHom f
      change (1 : Fin 2) ≤ 0 at h
      exact (by omega : False).elim
    · rfl

/-- 概要：標準比較の図式の族の Hom の作用を単体集合の射にする。
方針：始点は恒等作用、終点は解像の豊穣作用の単体的自然性を使う。
規約：値域は二点の strict な図式の変換空間。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較の族の豊穣関手の写像部分。 -/
noncomputable def coherentResolutionArrowMappingSpaceMap (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (ihom X.obj).obj Y.obj ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
      (coherentResolutionArrowDiagram X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (coherentResolutionArrowDiagram Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) where
  app _ := ↾coherentResolutionArrowMappingSimplex X Y
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro η
    apply Subtype.ext
    funext i
    rcases i with ⟨i⟩
    fin_cases i
    · rfl
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionEnrichedMap X.obj Y.obj).app m (((ihom X.obj).obj Y.obj).map α η) =
        ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj X.obj)).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Y.obj)).map α
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionEnrichedMap X.obj Y.obj).app n η)
      exact congrArg (fun f : ((ihom X.obj).obj Y.obj).obj n ⟶
        ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj X.obj)).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Y.obj)).obj m ↦ f η)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionEnrichedMap X.obj Y.obj).naturality α)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
