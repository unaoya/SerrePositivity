module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallLeftFibrationModels
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.HTT.Section2_1_3.VertexFiberOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOppositeFibration

/-!
概要：right fibration の小さい全空間模型を反転から構成する。
方針：fiber の小さい Kan 模型を反転し、left fibration の縮小を全空間へ戻す。
規約：全空間の同値を構成し、頂点族だけの縮小にはしない。
使われ方：小さい始域族上の対象への comma の宇宙制御。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：小さい Kan 模型を持つ空間の反転も小さい Kan 模型を持つ。
方針：同じ模型と全同値を反転し、宇宙変更との同型を合成する。
規約：元の全空間を保持する。
使われ方：right fibration の fiber を left fibration 側へ移す。 -/
lemma smallKanModel_op {X : SSet.{u + 1}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel X.op := by
  obtain ⟨K, ⟨e⟩⟩ := hX
  exact ⟨⟨K.obj.op, inferInstance⟩,
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} K.obj)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOpposite e)⟩⟩

/-- 概要：小さい底と小さい Kan fiber を持つ right fibration の全空間は小模型を持つ。
方針：反転した fiber の小ささを保ち、left fibration の縮小後に再び反転する。
規約：元の right fibration 自体の次数ごとの小ささを要求しない。
使われ方：compact 始域を持つ comma の小模型。 -/
lemma exists_smallRightFibrationModel_of_small_base
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    [∀ n, Small.{u} (B.obj n)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (hp : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) E) := by
  have hop : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers (SSet.opFunctor.map p) := by
    intro b
    exact (smallKanModel_op (hp (SSet.opObjEquiv b))).of_equivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso p (SSet.opObjEquiv b)))
  have (n : SimplexCategoryᵒᵖ) : Small.{u} (B.op.obj n) :=
    inferInstanceAs (Small.{u} (B.obj _))
  obtain ⟨A, hA, ⟨a⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallLeftFibrationModel_of_small_base
    (SSet.opFunctor.map p) hop
  have := hA
  exact ⟨A.op, inferInstance,
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} A)).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOpposite a).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (SSet.opFunctorCompOpFunctorIso.app E)))⟩⟩

/-- 概要：小さい模型を持つ底上の right fibration は小さい Kan fiber から小模型を持つ。
方針：底の模型も反転して left fibration の全空間比較へ渡す。
規約：底と全空間の次数ごとの小ささを要求しない。
使われ方：compact 全部分圏上の comma の縮小。 -/
lemma exists_smallRightFibrationModel_of_base_model
    {K : SSet.{u}} [Quasicategory K]
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (hp : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K) B) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) E) := by
  have hop : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers (SSet.opFunctor.map p) := by
    intro b
    exact (smallKanModel_op (hp (SSet.opObjEquiv b))).of_equivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso p (SSet.opObjEquiv b)))
  let eo := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} K)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOpposite e)
  obtain ⟨A, hA, ⟨a⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallLeftFibrationModel_of_base_model
    (SSet.opFunctor.map p) hop eo
  have := hA
  exact ⟨A.op, inferInstance,
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} A)).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOpposite a).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (SSet.opFunctorCompOpFunctorIso.app E)))⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
