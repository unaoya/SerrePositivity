module

public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanBoundary
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：元の両端点を固定した分母付き span の実単体集合から、局所化後の写像空間へ評価する。
方針：span の境界図式の指定頂点上の fiber を取り、分数評価の境界保存を移す。
規約：写像空間は区間模型。比較の同値性はまだ主張しない。
使われ方：分数による局所化の写像空間計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def fixedMarkedSpans (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) : SSet.{u} :=
  vertexFiber (markedSpanBoundary X W) (functorVertex (intervalMappingBoundary x y))

def fixedMarkedSpanInclusion (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    fixedMarkedSpans X W x y ⟶ markedSpans X W :=
  vertexFiberι (markedSpanBoundary X W) (functorVertex (intervalMappingBoundary x y))

lemma intervalMappingBoundary_postcomp {X Q : SSet.{u}} (F : X ⟶ Q) (x y : X _⦋0⦌) :
    intervalMappingBoundary x y ≫ F =
      intervalMappingBoundary (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change F.app (Opposite.op ⦋n⦌)
      (if s.val 0 = 0 then PinchedHom.constant x n else PinchedHom.constant y n) =
    if s.val 0 = 0 then PinchedHom.constant (F.app (Opposite.op ⦋0⦌) x) n else
      PinchedHom.constant (F.app (Opposite.op ⦋0⦌) y) n
  split_ifs
  · exact ConcreteCategory.congr_hom
      (F.naturality (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op) x
  · exact ConcreteCategory.congr_hom
      (F.naturality (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op) y

def fixedFractionEvaluation {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x y : X _⦋0⦌) :
    fixedMarkedSpans X W x y ⟶
      intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _ (fixedMarkedSpanInclusion X W x y ≫ fractionSpanEvaluation F W hF) (by
    rw [Category.assoc, fractionSpanEvaluation_boundary, ← Category.assoc,
      fixedMarkedSpanInclusion, vertexFiberι_comp, SSet.const_comp]
    change SSet.const (functorVertex (intervalMappingBoundary x y ≫ F)) = _
    rw [intervalMappingBoundary_postcomp])

lemma fixedFractionEvaluation_inclusion {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x y : X _⦋0⦌) :
    fixedFractionEvaluation F W hF x y ≫
      vertexFiberι ((pre (boundary 1).ι).app Q)
        (functorVertex (intervalMappingBoundary (F.app (Opposite.op ⦋0⦌) x)
          (F.app (Opposite.op ⦋0⦌) y))) =
      fixedMarkedSpanInclusion X W x y ≫ fractionSpanEvaluation F W hF :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.KST.LocalizingInvariants
