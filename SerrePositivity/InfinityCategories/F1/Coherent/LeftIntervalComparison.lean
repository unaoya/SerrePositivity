module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftPrismEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.PrismEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConstantFiber
public import SerrePositivity.InfinityCategories.Core.PrismOpposite

/-!
概要：反転した右 coherent Hom の区間族と既存の左 Hom の区間族の厳密な比較。
方針：両方の族を同じ coherent 単体の切断制限として計算する。
規約：係数の反転と ULift の交換を明示し、Kan 性を仮定しない。
使われ方：pointed-space の普遍輸送で用いた辺を、既存の左 Hom の辺に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 左 pinched 模型の fiber 同型は、元の標準単体の座標を保つ。 -/
lemma pinchedLeftCosliceFiberIso_simplex {X : SSet.{u}} (x y : X _⦋0⦌) (n : ℕ)
    (s : (pinchedHomLeft x y) _⦋n⦌) :
    cosliceFiberSimplex n ((pinchedLeftCosliceFiberIso x y).hom.app (Opposite.op ⦋n⦌) s) =
      pinchedLeftSimplexVal n s :=
  cosliceFiberSimplex_equiv_symm n ((pinchedLeftSimplexEquiv x y n) s)

/-- 反転した豊穣 Hom を、既存の左 coslice fiber の区間比較で展開した族。 -/
def coherentLeftHomInterval {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) : Δ[1] ⊗ ((SSet.uliftFunctor.{v, u}).obj
      (SimplicialCategory.sHom X Y)).op ⟶ SimplicialNerve C :=
  intervalMappingUncurry
    ((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom X Y)).inv ≫
      HomotopyLimits.coherentCosliceFiberComparison X Y ≫
        cosliceFiberToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y))

/-- 左 coherent Hom の区間族の各単体は、反転した右 coherent 単体の左切断。 -/
lemma coherentLeftHomInterval_evaluate {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) {n : ℕ}
    (a : ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) :
    (coherentLeftHomInterval X Y).app (Opposite.op ⦋n⦌) (t, a) =
      (SimplicialNerve C).map
        (SimplexCategory.mkHom (coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom)).op
        (HomotopyLimits.coherentOppositeInverseSimplex
          (coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X)
            (SSet.opObjEquiv a).down)) := by
  change (intervalMappingUncurry
    (((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom X Y)).inv ≫
      HomotopyLimits.coherentCosliceFiberComparison X Y) ≫
      cosliceFiberToIntervalMappingSpace (coherentNerveVertex X)
        (coherentNerveVertex Y))).app _ (t, a) = _
  rw [cosliceFiberToIntervalMappingSpace_evaluate]
  change (SimplicialNerve C).map _
    (cosliceFiberSimplex n ((pinchedLeftCosliceFiberIso (coherentNerveVertex X)
      (coherentNerveVertex Y)).hom.app _
        ((HomotopyLimits.coherentLeftHomComparison X Y).app _
          ((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom X Y)).inv.app _ a)))) = _
  rw [pinchedLeftCosliceFiberIso_simplex]
  exact congrArg ((SimplicialNerve C).map _) (HomotopyLimits.coherentLeftHomComparison_simplex
    X Y (((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom X Y)).inv.app _ a).down))

/-- 反対圏の右 Hom の区間族を反転して戻すと、既存の左 Hom の区間族そのものとなる。 -/
lemma coherentLeftHomInterval_eq_reverse {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    coherentLeftHomInterval X Y =
      reversePrism (intervalMappingUncurry (coherentHomComparison (Opposite.op Y) (Opposite.op X) ≫
        pinchedHomToIntervalMappingSpace _ _)) ≫
      SSet.opFunctor.map (HomotopyLimits.coherentNerveOppositeInverse C) ≫
      (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  rw [coherentLeftHomInterval_evaluate]
  change _ = HomotopyLimits.coherentOppositeInverseSimplex
    ((intervalMappingUncurry (coherentHomComparison (Opposite.op Y) (Opposite.op X) ≫
      pinchedHomToIntervalMappingSpace _ _)).app (Opposite.op ⦋n⦌)
        (stdSimplex.objEquiv.symm (SimplexCategory.mkHom
          (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom)), SSet.opObjEquiv a))
  rw [pinchedHomToIntervalMappingSpace_evaluate,
    HomotopyLimits.coherentOppositeInverseSimplex_naturality, coherentLeftPrismCut_eq_reverse]
  rfl

end SerrePositivity.InfinityCategories
