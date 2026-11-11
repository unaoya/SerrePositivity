module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitComparisonFiberReturn
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.PointwiseHomotopyPath

/-!
概要：順方向比較で導来 fiber の普遍データを制限すると元の標的・経路を回収する。
方針：頂点 fiber・path 置換の二射影を計算し、可逆 path の普遍ホモトピーを回収する。
規約：終点の等式だけでなく raw なホモトピーの一致を保つ。
使われ方：B1 の普遍族から定義した戻る比較射との合成。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：Kan 複体内のホモトピーを可逆 path にして普遍ホモトピーへ戻すと元の射。
方針：全辺が可逆である場合の点ごとの持ち上げの回収公式を使う。
規約：ホモトピーの代表を厳密に回収する。
使われ方：順方向比較で普遍ホモトピーを制限する。 -/
lemma homotopyEquivalencePath_homotopy {A Z : SSet.{u}} [KanComplex Z]
    {f g : A ⟶ Z} (H : SSet.Homotopy f g) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyEquivalencePath H ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy Z).h = H.h := by
  have hi : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H v).toTruncated := by
    intro v
    change IsIso _
    exact IsGroupoid.all_isIso (C := hoFunctor.obj Z) _
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath_homotopy H hi

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- 概要：順方向比較で導来 fiber の普遍標的族を制限すると元の標的族。
方針：順方向比較の第二射影の公式を略記に合わせる。
規約：射の厳密な等式。
使われ方：普遍復元の前合成の始点の認識。 -/
lemma unitCommaMappingToComparisonFiber_source
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaMappingToComparisonFiber η x w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComparisonFiberSource η x w =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSquareTargetFamily η x w
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquare (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) w))) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComparisonFiberSource, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaMappingToComparisonFiber_projection η x w

/-- 概要：順方向比較で導来 fiber の普遍 path を制限すると元のホモトピーの path。
方針：頂点 fiber の包含と path 置換の第一射影を計算する。
規約：path 自体の厳密な一致。
使われ方：普遍復元を制限した境界 path の認識。 -/
lemma unitCommaMappingToComparisonFiber_path
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaMappingToComparisonFiber η x w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComparisonFiberPath η x w =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyEquivalencePath (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaMappingComparisonHomotopy η x w) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComparisonFiberPath, ← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _) ≫ pullback.fst _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  exact pullback.lift_fst _ _ _

/-- 概要：順方向比較で普遍ホモトピーを制限すると元のホモトピーの射そのもの。
方針：path の射影と可逆 path の普遍ホモトピーの回収を使う。
規約：単に同じ Hom の類を表すという主張には弱めない。
使われ方：戻る比較射の前合成を元の正方形の復元と照合する。 -/
lemma unitCommaMappingToComparisonFiber_homotopy
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaMappingComparisonHomotopy η x w).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaMappingToComparisonFiber η x w ▷ (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComparisonFiberHomotopy η x w).h := by
  change _ = (_ ▷ _) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComparisonFiberPath η x w ▷ _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy _).h)
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
    unitCommaMappingToComparisonFiber_path, homotopyEquivalencePath_homotopy]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
