module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentLeftHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.UniverseHomotopyReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedSpaceMappingSpaces

/-!
概要：Kan 複体とその単体集合の反転の実際の同値。
方針：豊穣 Hom の左右の pinched 比較を合成し、一点空間からの Hom で任意の Kan 複体に適用する。
規約：選んだ同値の逆を含む。反転の二重適用や射についての厳密な自然性は主張しない。
使われ方：HTT 4.2.4.1、導来 fiber 全体の反転を外す比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：反転した豊穣 Hom の ULift から元の豊穣 Hom の ULift への実際の射。
方針：左 pinched 模型への比較、左右の模型の同値、右 Hom の比較の逆を合成する。
規約：局所 Kan 性を要求し、選んだ逆を含む。
使われ方：任意の Kan 複体の反転を一点からの Hom として外す。 -/
def coherentHomOppositeComparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (x y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y).op ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftHomComparison x y ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftRightEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence x y).inv

/-- 概要：左右の pinched 模型を介する反転した豊穣 Hom の比較はホモトピー同値。
方針：三つの構成済みの同値性を合成する。
規約：追加の fibration 性や可縮性は要求しない。
使われ方：反転を外す射を元の宇宙へ降下する際の同値性。 -/
lemma coherentHomOppositeComparison_homotopyEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coherentHomOppositeComparison x y) := by
  let h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftRightEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y))
  let h₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence x y).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftHomComparison_homotopyEquivalence x y).comp
    (h₂.isQCatEquivalence.isSimplicialHomotopyEquivalence.comp
      h₃.isQCatEquivalence.isSimplicialHomotopyEquivalence)

/-- 概要：任意の Kan 複体の反転から元の複体への実際の射。
方針：一点空間からの豊穣 Hom の反転比較を内部 Hom の同型で挟み、ULift の充満性で戻す。
規約：元の宇宙の射を返し、射 K.op ⟶ K の選択を固定する。
使われ方：導来 fiber 全体の反転を外す実際の同値の順射。 -/
def kanOppositeComparison (K : SSet.{u}) [KanComplex K] : K.op ⟶ K :=
  (SSet.uliftFunctor.{u + 1, u}).preimage
    ((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso (⟨K, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})).inv) ≫
      coherentHomOppositeComparison _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (⟨K, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso (⟨K, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})).hom)

/-- 概要：反転した Kan 複体から元の複体への構成済みの射はホモトピー同値。
方針：ULift 後の三つの同値の合成を、完全忠実性とホモトピーの降下によって元へ戻す。
規約：Kan 性だけを要求し、非空性や可縮性は要求しない。
使われ方：HTT 4.2.4.1、元の導来 fiber の反転を取り除く。 -/
lemma kanOppositeComparison_homotopyEquivalence (K : SSet.{u}) [KanComplex K] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (kanOppositeComparison K) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_ulift.{u, u + 1}
  dsimp only [kanOppositeComparison]
  rw [CategoryTheory.Functor.map_preimage]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso _).comp
    ((coherentHomOppositeComparison_homotopyEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject
      (⟨K, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso _))

/-- 概要：任意の Kan 複体はその反転と同じ宇宙で圏同値。
方針：構成済みの反転を外す射のホモトピー同値性から逆と二つの可逆二胞体を選ぶ。
規約：空の Kan 複体も含み、自然な比較であることは主張しない。
使われ方：pinched Hom と元の非反転 q_x の反転なしの導来 fiber の比較。 -/
def kanOppositeEquivalence (K : SSet.{u}) [KanComplex K] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence K.op K :=
  (kanOppositeComparison_homotopyEquivalence K).isQCatEquivalence.choose

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
