module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpecifiedCofiberSpan

/-!
概要：元の任意の矢印族を、第二枝の終点が零である span の全単体族へ延長する。
方針：零対象へ向かう辺の始点評価の厳密な切断を使う。
規約：元の第一枝を厳密に保持する。使われ方：全単体上の差の cofiber 関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily

variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

def zeroArrowSection : X ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrows X :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X))

lemma zeroArrowSection_source : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection X ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X = 𝟙 X :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X))

variable {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

def zeroArrow : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection X ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow).ι

lemma zeroArrow_source : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrow X a ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection X ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow).ι) ≫ _ = _
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection X) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection_source, Category.comp_id]

def span : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows a (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrow X a) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrow_source X a).symm

lemma span_left : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span X a ≫ (pre horn₂₀.ι₀₁).app X = a := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left _ _ _

lemma span_right : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span X a ≫ (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrow X a :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right _ _ _

lemma span_vertex_zero (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((horn₂₀.ι₀₂ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span X a).app _ x)).app
        (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span X a).app _ x)
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span X a).app _ x :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ d)))
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₂).app X).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)))
  rw [hd]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span X a ≫ (pre horn₂₀.ι₀₂).app X) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app _ x)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span_right]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection X).app _ x)

lemma span_hasColimit (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span X a).app _ x)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_span_of_zero_second _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span_vertex_zero X a x)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span_hasColimit := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span_hasColimit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span_left := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span_right := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span_vertex_zero := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span_vertex_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrow := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrow

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrowSection := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrowSection_source := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrow_source := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrow_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.span._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrow._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrow._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrowSection._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroArrowSection._proof_1
