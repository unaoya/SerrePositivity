module

public import SerrePositivity.KST.Spectra.D3FiberPathIsoComparison

/-!
概要：既存の path 補正成分同型が、持ち上げた同じ指定 path の辺の類に一致すると認証。
方針：元の fiber 比較の値を回収し、端点表示だけを輸送して exact 表示と照合する。
規約：既存 componentIso の選択を置き換えない。使われ方：元の切断補正の終点値の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 元の path を uncurry して作る同じ lift は、全単体で元の path そのもの。 -/
lemma d3EquivalencePathLift_uncurry {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y)
    (hH : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((uncurry (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceHomotopyPathLift (uncurry (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)) hH = L := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceHomotopyPathLift_ι
    (uncurry (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)) hH).trans (curry_uncurry (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y))
  exact (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj Y)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex).ι).1 h

/-- 既存の Kan path 族から作る同型は、元の同じ path の指定同型に一致する。 -/
lemma d3KanEquivalencePathFunctorIso_value {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanEquivalencePath_functorIso L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathFamilyIso L) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanEquivalencePath_functorIso
  refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
  refine (d3TrivialPathFiberIso_value _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ uncurry (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)) _).trans ?_
  apply d3EquivalencePathFamilyIso_of_eq
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj Y)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex).ι).1
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι] using (curry_uncurry (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y))

/-- 関手同型の同じ順射の値と端点表示は、同型全体の型付き一致を決める。 -/
lemma d3FunctorIso_heq_of_hom_heq {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hf : f = f') (hg : g = g')
    (hh : HEq e.hom e'.hom) : HEq e e' := by
  subst f' g'
  exact heq_of_eq (Iso.ext (eq_of_heq hh))

section
variable {A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
  {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)}
  (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e)

/-- 元の既存 componentIso は、同じ指定 path の同型の端点表示に一致する。 -/
lemma d3PathCorrectedComponentIso_value :
    HEq s.componentIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathFamilyIso s.path) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare.componentIso
  refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
  exact d3KanEquivalencePathFunctorIso_value s.path

/-- 同じ exact 表示も、同じ指定 path の同型の同じ順射を保持する。 -/
lemma d3PathCorrectedExactComponentIso_value :
    HEq s.exactComponentIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathFamilyIso s.path) := by
  apply d3FunctorIso_heq_of_hom_heq _ _ s.zero.symm s.one.symm
  change HEq (SSet.Truncated.HomotopyCategory.homMk s.componentEdge.toTruncated)
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathFamilyEdge s.path).toTruncated)
  exact d3HomMk_heq _ _ (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.zero.symm)
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.one.symm) rfl

/-- 元の選択を変更せず、既存 componentIso と同じ path による exact 表示の一致を認証。 -/
lemma d3PathCorrectedComponentIso_eq_exact : s.componentIso = s.exactComponentIso := by
  exact eq_of_heq ((d3PathCorrectedComponentIso_value s).trans
    (d3PathCorrectedExactComponentIso_value s).symm)

/-- 既存 componentIso の標的像も、元の指定自然性同型そのものを回収する。 -/
lemma d3PathCorrectedComponentIso_postcomp :
    s.componentIso.postcomp q =
      eqToIso (congrArg
        (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) s.comm) ≪≫ e := by
  rw [d3PathCorrectedComponentIso_eq_exact]
  exact s.exactComponentIso_postcomp
end

end SerrePositivity.KST.Spectra
