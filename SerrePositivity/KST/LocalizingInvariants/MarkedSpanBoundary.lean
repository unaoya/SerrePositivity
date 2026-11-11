module

public import SerrePositivity.KST.LocalizingInvariants.FractionTriangleEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace

/-!
概要：分母付き span の二つの終点を区間の境界図式にまとめ、分数評価が境界を保つと示す。
方針：三角形の二端点の厳密な式を、内部 Hom と区間境界の普遍性へ移す。
規約：境界は全単体で保存する。使われ方：両端を固定した分数の写像空間への評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def markedSpanSource (X : SSet.{u}) (W : Set (X _⦋1⦌)) : markedSpans X W ⟶ X :=
  markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

def markedSpanTarget (X : SSet.{u}) (W : Set (X _⦋1⦌)) : markedSpans X W ⟶ X :=
  markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₂).app X ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

def markedSpanBoundary (X : SSet.{u}) (W : Set (X _⦋1⦌)) :
    markedSpans X W ⟶ (ihom (boundary 1 : SSet.{u})).obj X :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (markedSpanSource X W) (markedSpanTarget X W))

lemma intervalFunctor_restrict_boundary {A Y : SSet.{u}}
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj Y) :
    f ≫ (pre (boundary 1).ι).app Y = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
      (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict]
  simp only [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]

lemma intervalBoundaryDiagram_postcomp {A X Y : SSet.{u}} (f g : A ⟶ X) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (f ≫ F) (g ≫ F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a⟩
  change F.app (Opposite.op ⦋n⦌)
    (if s.val 0 = 0 then f.app _ a else g.app _ a) =
    if s.val 0 = 0 then F.app _ (f.app _ a) else F.app _ (g.app _ a)
  split_ifs <;> rfl

lemma fractionSpanEvaluation_boundary {X Q : SSet.{u}} [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) :
    fractionSpanEvaluation F W hF ≫ (pre (boundary 1).ι).app Q =
      markedSpanBoundary X W ≫ (ihom (boundary 1 : SSet.{u})).map F := by
  rw [intervalFunctor_restrict_boundary, markedSpanBoundary, ← curry_natural_right,
    intervalBoundaryDiagram_postcomp, fractionSpanEvaluation_source, fractionSpanEvaluation_target]
  congr 1

end SerrePositivity.KST.LocalizingInvariants
