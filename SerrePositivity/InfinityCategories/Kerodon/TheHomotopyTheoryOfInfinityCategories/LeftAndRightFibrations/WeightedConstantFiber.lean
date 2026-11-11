module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ReflectedPathCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber

/-!
概要：構成済みの weighted nerve の比較を一定の底の上で終点固定の fiber へ持ち上げる。
方針：係数の一定の底への包含を比較射へ合成し、射影の定値性から fiber に制限する。
規約：始域は反転した sHom(x,F(i)) の ULift のまま。
使われ方：HTT 4.2.4.1 の実際の比較射の fiber と標準 Hom 比較の同定。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：反転した豊穣 Hom を一定の底の上の係数として左 coslice へ写す。
方針：weighted nerve の一定の底への包含と構成済みの比較射を合成する。
規約：始域と終域の固定対象は x と F(i)。
使われ方：HTT 4.2.4.1 の具体的な fiber 比較の順方向。 -/
noncomputable def weightedConstantCosliceMap (F : I ⥤ C) (x : C) (i : I) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) :=
  (SSet.uliftFunctor.{v, u}).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x

/-- 概要：一定の底への比較射の終点は F(i) の標準頂点に定値。
方針：weighted nerve の射影の式と strict な図式の頂点の式を使う。
規約：終点の定値性は全次数での厳密な式。
使われ方：HTT 4.2.4.1 の左 coslice の fiber への持ち上げ条件。 -/
lemma weightedConstantCosliceMap_projection (F : I ⥤ C) (x : C) (i : I) :
    weightedConstantCosliceMap F x i ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i)) := by
  dsimp only [weightedConstantCosliceMap]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison_over, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift_projection]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F).app (Opposite.op ⦋n⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i)) n
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i = ComposableArrows.mk₀ i := ComposableArrows.ext₀ rfl
  exact congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z n)
    (Eq.trans (congrArg
      (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F).app (Opposite.op ⦋0⦌) (ULift.up z)) hv)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F i))

/-- 概要：一定の底への比較射を終点 F(i) の fiber へ持ち上げる。
方針：終点の定値性に fiber の普遍的な持ち上げを適用する。
規約：Kan 性なしで実際の射を定義する。
使われ方：HTT 4.2.4.1 の標準 Hom 比較との同定と同値性の移送。 -/
noncomputable def weightedConstantCosliceFiberMap (F : I ⥤ C) (x : C) (i : I) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (weightedConstantCosliceMap F x i)
    (weightedConstantCosliceMap_projection F x i)

/-- 概要：一定の底の fiber 比較の元の simplex は係数から組み立てた cone simplex。
方針：fiber の持ち上げと左 coslice の座標を展開し、join の同型の往復を消去する。
規約：s は反転した sHom の n 単体であり、始域に ULift.up で入れる。
使われ方：HTT 4.2.4.1 の具体的な fiber 比較と既存の Hom 比較の成分の同定。 -/
lemma weightedConstantCosliceFiberMap_simplex (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n
      ((weightedConstantCosliceFiberMap F x i).app (Opposite.op ⦋n⦌) (ULift.up s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i s) := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i s)))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]


/-- 概要：一定の底の cone の非定値 Hom は反転した path の右最大点による標準評価。
方針：cone の初点からの Hom を展開し、一定係数の反転の座標式を使う。
規約：元の反転した豊穣 Hom の n 単体 s と正頂点 j.succ を固定する。
使われ方：HTT 4.2.4.1 の fiber 比較と右 Hom の既存の比較の照合。 -/
lemma weightedConstantConeHom_zero_succ (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeHom F x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i s)
      0 j.succ =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reflectedFirstPathFunctor j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j.rev ≫
      SSet.yonedaEquiv.symm (SSet.opObjEquiv s) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
      SSet.yonedaEquiv.symm s) = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reflectedConstantCoefficient s j

/-- 概要：既存の左 Hom 比較の元の simplex は反対圏の標準右 Hom simplex の反転。
方針：比較の定義を展開し、pinched Hom の端点移送が値を変えないことを使う。
規約：パラメータと元の nerve の二つの反転を明示する。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の実際の fiber 射との同定。 -/
lemma coherentLeftHomComparison_simplex (x y : C) {n : ℕ}
    (s : (SimplicialCategory.sHom x y).op _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftHomComparison x y).app (Opposite.op ⦋n⦌) (ULift.up s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeInverseSimplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (X := Opposite.op y) (Y := Opposite.op x)
        (SSet.opObjEquiv s)) := by
  change SSet.opObjEquiv
    (((eqToHom (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := (SimplicialNerve C).op) a b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse_vertex y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse_vertex x))).app
      (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse C)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op x))).app
          (Opposite.op ⦋n⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison (Opposite.op y) (Opposite.op x)).app
            (Opposite.op ⦋n⦌) (ULift.up (SSet.opObjEquiv s))))).val) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_endpointTransport_val
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse_vertex y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse_vertex x)]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
