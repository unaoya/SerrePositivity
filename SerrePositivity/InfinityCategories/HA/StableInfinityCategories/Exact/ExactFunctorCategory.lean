module
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice
/-!
概要：完全関手と指定頂点を零化する完全関手の全 ∞ 部分圏を構成する。
方針：既存の実関手単体集合の頂点条件による全部分複体を使う。
規約：自然変換を制限せず全て保持。使われ方：Verdier 列の全完全関手圏の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 実関手頂点が、元の同じ完全関手を表す条件。 -/
def IsExactFunctorVertex (X Y : SSet.{u}) (v : ((ihom X).obj Y) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).symm v)
/-- 完全関手の全 ∞ 部分圏。 -/
def exactFunctors (X Y : SSet.{u}) : ((ihom X).obj Y).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsExactFunctorVertex X Y)
/-- 指定頂点を零化する完全関手を表す、元の実関手圏の頂点条件。 -/
def IsZeroingExactFunctorVertex (X Y : SSet.{u}) (P : Set (X _⦋0⦌))
    (v : ((ihom X).obj Y) _⦋0⦌) : Prop :=
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).symm v
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F ∧ ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)
/-- 指定頂点を零化する完全関手の全 ∞ 部分圏。 -/
def zeroingExactFunctors (X Y : SSet.{u}) (P : Set (X _⦋0⦌)) :
    ((ihom X).obj Y).Subcomplex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsZeroingExactFunctorVertex X Y P)
/-- 完全関手の全 ∞ 部分圏は quasicategory。 -/
instance exactFunctors_quasicategory (X Y : SSet.{u}) [Quasicategory Y] :
    Quasicategory (exactFunctors X Y : SSet.{u}) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom X).obj Y) (IsExactFunctorVertex X Y) : SSet.{u}))
/-- 零化完全関手の全 ∞ 部分圏は quasicategory。 -/
instance zeroingExactFunctors_quasicategory (X Y : SSet.{u}) [Quasicategory Y]
    (P : Set (X _⦋0⦌)) : Quasicategory (zeroingExactFunctors X Y P : SSet.{u}) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom X).obj Y)
    (IsZeroingExactFunctorVertex X Y P) : SSet.{u}))
/-- 完全関手条件は、同じ実関手頂点で元の条件を回収する。 -/
lemma isExactFunctorVertex_functorVertex (X Y : SSet.{u}) (F : X ⟶ Y) :
    IsExactFunctorVertex X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y) F)) ↔ _
  rw [Equiv.symm_apply_apply]
/-- 零化完全関手条件は、同じ実関手頂点で元の二条件を回収する。 -/
lemma isZeroingExactFunctorVertex_functorVertex (X Y : SSet.{u}) (P : Set (X _⦋0⦌))
    (F : X ⟶ Y) : IsZeroingExactFunctorVertex X Y P (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F ∧ ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) := by
  change (let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y) F);
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G ∧ ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (G.app (Opposite.op ⦋0⦌) x)) ↔ _
  rw [Equiv.symm_apply_apply]
/-- 指定頂点を零化する完全関手による、全完全関手圏の実前合成。 -/
def zeroingExactPrecomposition {X Q : SSet.{u}} (q : X ⟶ Q) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q]
    (P : Set (X _⦋0⦌)) (hq : ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.app (Opposite.op ⦋0⦌) x))
    (Y : SSet.{u}) : (exactFunctors Q Y : SSet.{u}) ⟶
      (zeroingExactFunctors X Y P : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (IsZeroingExactFunctorVertex X Y P)
    ((exactFunctors Q Y).ι ≫ (pre q).app Y) (by
      intro v
      let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Q Y).symm v.val
      have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Q Y).apply_symm_apply v.val
      have he : ((exactFunctors Q Y).ι ≫ (pre q).app Y).app (Opposite.op ⦋0⦌) v =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (q ≫ G) := congrArg (((pre q).app Y).app (Opposite.op ⦋0⦌)) hv.symm
      apply (congrArg (IsZeroingExactFunctorVertex X Y P) he).mpr
      apply (isZeroingExactFunctorVertex_functorVertex X Y P (q ≫ G)).mpr
      refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp q G, fun x hx => ?_⟩
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := G) _ (hq x hx))
/-- 零化完全関手への前合成は、元の全関手圏の同じ前合成への制限。 -/
lemma zeroingExactPrecomposition_ι {X Q : SSet.{u}} (q : X ⟶ Q) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q]
    (P : Set (X _⦋0⦌)) (hq : ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.app (Opposite.op ⦋0⦌) x))
    (Y : SSet.{u}) : zeroingExactPrecomposition q P hq Y ≫ (zeroingExactFunctors X Y P).ι =
      (exactFunctors Q Y).ι ≫ (pre q).app Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
