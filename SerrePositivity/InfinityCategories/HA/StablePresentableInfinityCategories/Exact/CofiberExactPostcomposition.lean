module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.ExactArrowMap

/-!
概要：完全関手は普遍 cofiber 四角形の全族を、指定した底辺と cofiber 頂点ごと写す。
方針：零角と押し出しの保存で全部分複体に持ち上げ、評価との交換を保持する。
規約：全単体上の関手を構成する。使われ方：cofiber 関手の coherent な自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
namespace SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
variable {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]

omit [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] in
lemma squareDiagram_postcomp
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v ≫ F := by
  obtain ⟨R, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).surjective v
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (R ≫ F)) = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R) ≫ F
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply (R ≫ F)).trans
    (congrArg (· ≫ F) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply R).symm)

def postcomp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.Predicate (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion X ≫ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F) (by
    intro v
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram
      (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v.val)) 0 1) ∧ _
    rw [_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.squareDiagram_postcomp]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F) _ hv.1,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare F _ hv.2⟩)

lemma postcomp_inclusion : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion Y =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion X ≫ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

lemma postcomp_bottom : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Y =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X ≫ (ihom (Δ[1] : SSet.{u})).map F := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_inclusion]
  rw [Category.assoc, (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).naturality F]
  rfl

lemma postcomp_right : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Y =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X ≫ (ihom (Δ[1] : SSet.{u})).map F := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_inclusion]
  rw [Category.assoc, (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).naturality F]
  rfl

lemma postcomp_cofiber : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ F := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_right, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.postcomp := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.postcomp_bottom := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.postcomp_cofiber := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_cofiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.postcomp_inclusion := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.postcomp_right := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.squareDiagram_postcomp := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.squareDiagram_postcomp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.postcomp._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp._proof_1
