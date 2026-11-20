module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyFiber

/-! # 元の恒等 span を、両端固定の実分数空間の点として保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {X : SSet.{u}} (W : Set (X _⦋1⦌)) (x : X _⦋0⦌)
  (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 ∈ W)

/-- 恒等の両脚を持つ元の定値 span は、指定された分母条件を持つ実頂点。 -/
def identityMarkedSpan : (markedSpans X W) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : (horn 2 0 : SSet.{u}) ⟶ X), by
    intro a
    have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [ha, op_id, Functor.map_id_apply]
    exact hx⟩

/-- 元の恒等 span の第一終点は、指定した同じ頂点そのもの。 -/
theorem identityMarkedSpan_source :
    (markedSpanSource X W).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan W x hx) = x := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0 = x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x

/-- 元の恒等 span の第二終点も、同じ頂点そのもの。 -/
theorem identityMarkedSpan_target :
    (markedSpanTarget X W).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan W x hx) = x := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0 = x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x

/-- 元の第一終点を固定した全 span 族の恒等点。 -/
def identityMarkedSpanFamily : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan W x hx, by
    change (markedSpanSource X W).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan W x hx) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan_source W x hx).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x).symm⟩

/-- 元の可変第二終点への射影も恒等点で同じ頂点を回収する。 -/
theorem identityMarkedSpanFamily_projection :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpanFamily W x hx) = x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan_target W x hx

/-- 両端固定の元の分数 fiber の恒等点。 -/
def identityMarkedSpanFamilyFiber :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) x) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpanFamily W x hx, by
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpanFamily W x hx) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpanFamily_projection W x hx).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x).symm⟩

/-- 同じ恒等点を、元の境界条件で定義した両端固定分数空間へ移す。 -/
def identityFixedMarkedSpan : (fixedMarkedSpans X W x x) _⦋0⦌ :=
  (markedSpanFamilyFiberIso X W x x).inv.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpanFamilyFiber W x hx)

/-- 元の span 圏への包含は、同じ恒等 span の実際の頂点を厳密に回収する。 -/
theorem identityFixedMarkedSpan_inclusion :
    (fixedMarkedSpanInclusion X W x x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityFixedMarkedSpan W x hx) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan W x hx := by
  exact congrArg (fun m => m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpanFamilyFiber W x hx))
    (markedSpanFamilyFiberToFixed_inclusion X W x x)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
