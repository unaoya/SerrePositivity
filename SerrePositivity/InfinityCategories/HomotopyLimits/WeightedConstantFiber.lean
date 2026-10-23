module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedPathCoordinates
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveFiber

/-!
概要：構成済みの weighted nerve の比較を一定の底の上で終点固定の fiber へ持ち上げる。
方針：係数の一定の底への包含を比較射へ合成し、射影の定値性から fiber に制限する。
規約：始域は反転した sHom(x,F(i)) の ULift のまま。
使われ方：HTT 4.2.4.1 の実際の比較射の fiber と標準 Hom 比較の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：反転した豊穣 Hom を一定の底の上の係数として左 coslice へ写す。
方針：weighted nerve の一定の底への包含と構成済みの比較射を合成する。
規約：始域と終域の固定対象は x と F(i)。
使われ方：HTT 4.2.4.1 の具体的な fiber 比較の順方向。 -/
noncomputable def weightedConstantCosliceMap (F : I ⥤ C) (x : C) (i : I) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op ⟶
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x)) :=
  (SSet.uliftFunctor.{v, u}).map
    (weightedNerveConstantLift (simplicialHomDiagram F x ⋙ SSet.opFunctor) i) ≫
      weightedCosliceComparison F x

/-- 概要：一定の底への比較射の終点は F(i) の標準頂点に定値。
方針：weighted nerve の射影の式と strict な図式の頂点の式を使う。
規約：終点の定値性は全次数での厳密な式。
使われ方：HTT 4.2.4.1 の左 coslice の fiber への持ち上げ条件。 -/
lemma weightedConstantCosliceMap_projection (F : I ⥤ C) (x : C) (i : I) :
    weightedConstantCosliceMap F x i ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)) =
    SSet.const (coherentNerveVertex (F.obj i)) := by
  dsimp only [weightedConstantCosliceMap]
  rw [Category.assoc, weightedCosliceComparison_over, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, weightedNerveConstantLift_projection]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (strictCoherentDiagram F).app (Opposite.op ⦋n⦌)
    (PinchedHom.constant (ULift.up (nerveVertex i)) n) =
      PinchedHom.constant (coherentNerveVertex (F.obj i)) n
  rw [pinchedConstant_map]
  have hv : nerveVertex i = ComposableArrows.mk₀ i := ComposableArrows.ext₀ rfl
  exact congrArg (fun z ↦ PinchedHom.constant z n)
    (Eq.trans (congrArg
      (fun z ↦ (strictCoherentDiagram F).app (Opposite.op ⦋0⦌) (ULift.up z)) hv)
      (strictCoherentDiagram_vertex F i))

/-- 概要：一定の底への比較射を終点 F(i) の fiber へ持ち上げる。
方針：終点の定値性に fiber の普遍的な持ち上げを適用する。
規約：Kan 性なしで実際の射を定義する。
使われ方：HTT 4.2.4.1 の標準 Hom 比較との同定と同値性の移送。 -/
noncomputable def weightedConstantCosliceFiberMap (F : I ⥤ C) (x : C) (i : I) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op ⟶
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
      (coherentNerveVertex (F.obj i)) :=
  vertexFiberLift _ _ (weightedConstantCosliceMap F x i)
    (weightedConstantCosliceMap_projection F x i)

/-- 概要：一定の底の fiber 比較の元の simplex は係数から組み立てた cone simplex。
方針：fiber の持ち上げと左 coslice の座標を展開し、join の同型の往復を消去する。
規約：s は反転した sHom の n 単体であり、始域に ULift.up で入れる。
使われ方：HTT 4.2.4.1 の具体的な fiber 比較と既存の Hom 比較の成分の同定。 -/
lemma weightedConstantCosliceFiberMap_simplex (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌) :
    cosliceFiberSimplex n
      ((weightedConstantCosliceFiberMap F x i).app (Opposite.op ⦋n⦌) (ULift.up s)) =
    weightedConeSimplex F x
      (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s) := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    ((leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (weightedConeSimplex F x
        (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s)))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]


/-- 概要：一定の底の cone の非定値 Hom は反転した path の右最大点による標準評価。
方針：cone の初点からの Hom を展開し、一定係数の反転の座標式を使う。
規約：元の反転した豊穣 Hom の n 単体 s と正頂点 j.succ を固定する。
使われ方：HTT 4.2.4.1 の fiber 比較と右 Hom の既存の比較の照合。 -/
lemma weightedConstantConeHom_zero_succ (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌) (j : Fin (n + 1)) :
    weightedConeHom F x
      (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s)
      0 j.succ =
    nerveMap (reflectedFirstPathFunctor j) ≫ pathLastMaximumMap j.rev ≫
      SSet.yonedaEquiv.symm (SSet.opObjEquiv s) := by
  change pathFirstMinimumMap j ≫ reflectedSimplexMap
    (stdSimplex.map (simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
      SSet.yonedaEquiv.symm s) = _
  exact reflectedConstantCoefficient s j

/-- 概要：既存の左 Hom 比較の元の simplex は反対圏の標準右 Hom simplex の反転。
方針：比較の定義を展開し、pinched Hom の端点移送が値を変えないことを使う。
規約：パラメータと元の nerve の二つの反転を明示する。
使われ方：Kerodon §4.6.7、HTT 4.2.4.1 の実際の fiber 射との同定。 -/
lemma coherentLeftHomComparison_simplex (x y : C) {n : ℕ}
    (s : (SimplicialCategory.sHom x y).op _⦋n⦌) :
    pinchedLeftSimplexVal n
      ((coherentLeftHomComparison x y).app (Opposite.op ⦋n⦌) (ULift.up s)) =
    coherentOppositeInverseSimplex
      (coherentHomComparisonSimplex (X := Opposite.op y) (Y := Opposite.op x)
        (SSet.opObjEquiv s)) := by
  change SSet.opObjEquiv
    (((eqToHom (congrArg₂ (fun a b ↦ pinchedHom (X := (SimplicialNerve C).op) a b)
      (coherentNerveOppositeInverse_vertex y) (coherentNerveOppositeInverse_vertex x))).app
      (Opposite.op ⦋n⦌)
      ((pinchedHomMap (coherentNerveOppositeInverse C)
        (coherentNerveVertex (Opposite.op y)) (coherentNerveVertex (Opposite.op x))).app
          (Opposite.op ⦋n⦌)
          ((coherentHomComparison (Opposite.op y) (Opposite.op x)).app
            (Opposite.op ⦋n⦌) (ULift.up (SSet.opObjEquiv s))))).val) = _
  rw [pinchedHom_endpointTransport_val
    (coherentNerveOppositeInverse_vertex y) (coherentNerveOppositeInverse_vertex x)]
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
