module

public import SerrePositivity.EInfinity.Interface.TensorUnitClasses
public import SerrePositivity.EInfinity.NativeBinaryCoconeHom

/-!
# 余積とテンソルの比較の二脚の条件

概要：HA 3.2.4.7 の関手全体の比較が指定余積錐の二脚を保つ条件を述べる。
方針：単位射の正規化された鎖写像の代表から標準テンソル射を定め、成分の可換式を要求する。
規約：全関手版の同型は別に保持し、ここではその成分と指定脚との適合性を記録する。
使われ方：BS の A2・A7 における指定された余極限錐の移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open scoped Simplicial

variable (S : Type u) [CommRing S] (E : EInfinityCore.{u})
  (x y : (E.CAlg S) _⦋0⦌) (P : E.CAlg S ⟶ E.CAlg S)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y)) (hv : c.vertex = atVertex P x)
  (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (P ≫ E.forget S) (E.forget S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.tensorWith (atVertex (E.forget S) y)))

/-- 全関手版の成分を、指定余錐の同じ頂点からの同型に正規化する。 -/
def tensorComparisonAtCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (atVertex (E.forget S) c.vertex)
      (atVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.tensorWith (atVertex (E.forget S) y)) (atVertex (E.forget S) x)) :=
  eqToIso (congrArg (fun z => SSet.HomotopyCategory.mk (atVertex (E.forget S) z)) hv) ≪≫ θ.app x

/-- HA 3.2.4.7 の指定二包含との適合条件。
単位代数からの各射について正規化された単位の代表が存在し、その代表による標準射に一致する。
EInfinityTheory では離散基底代数が始対象なので、単位射への量化は空ではない。 -/
def TensorCoproductLegCompatibility : Prop :=
  ∀ (ηx : (SSet.HomotopyCategory.mk (coreUnitVertex S E) : (E.CAlg S).HomotopyCategory) ⟶
        SSet.HomotopyCategory.mk x)
    (ηy : (SSet.HomotopyCategory.mk (coreUnitVertex S E) : (E.CAlg S).HomotopyCategory) ⟶
        SSet.HomotopyCategory.mk y),
  ∃ (unitX : 𝟙_ (Complex S) ⟶
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv S (atVertex (E.forget S) x)).val)
    (unitY : 𝟙_ (Complex S) ⟶
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv S (atVertex (E.forget S) y)).val),
    NormalizedTensorUnit S E x ηx unitX ∧ NormalizedTensorUnit S E y ηy unitY ∧
    (hoFunctor.map (E.forget S)).toFunctor.map (binaryCoconeLeftHom c) ≫
        (tensorComparisonAtCocone S E x y P c hv θ).hom =
      derivedTensorInlHom S (atVertex (E.forget S) x) (atVertex (E.forget S) y) unitY ∧
    (hoFunctor.map (E.forget S)).toFunctor.map (binaryCoconeRightHom c) ≫
        (tensorComparisonAtCocone S E x y P c hv θ).hom =
      derivedTensorInrHom S (atVertex (E.forget S) x) (atVertex (E.forget S) y) unitX

end SerrePositivity.EInfinity
