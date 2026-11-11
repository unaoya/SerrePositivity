module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopDiagramUniversalConeModel
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeSourceInitial
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeOpposite
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.VertexFiberMapIso

/-!
概要：普遍錐の選択を忘れ、全零隅四角形の始対象を得る。
方針：元の実引き戻しの同型と同じ頂点 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ固定頂点を保つ錐の比較 `loopDiagramUniversalConeIso_input`。 -/
lemma loopDiagramUniversalConeIso_input (X : SSet.{u}) [Quasicategory X] :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramUniversalConeIso X).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.universalConesOverProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X := by
  rw [← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ _ = _
  rw [pullback.lift_snd]
  rfl

/-- 同じ固定頂点を保つ錐の比較 `loopConeChoiceIso`。 -/
def loopConeChoiceIso (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjects X ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneChoiceObjects
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι :=
  asIso (pullback.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.universalConesOverProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι)
    (𝟙 _) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramUniversalConeIso X).hom (𝟙 _)
    (by simp) (by simpa only [Category.comp_id] using
      (loopDiagramUniversalConeIso_input X).symm))

/-- 同じ固定頂点を保つ錐の比較 `loopConeChoiceIso_diagram`。 -/
lemma loopConeChoiceIso_diagram (X : SSet.{u}) [Quasicategory X] :
    (loopConeChoiceIso X).hom ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.universalConesOverProjection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectDiagram X := by
  simp only [loopConeChoiceIso, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]

/-- 同じ固定頂点を保つ錐の比較 `loopConeChoiceFiber_hasInitial`。 -/
lemma loopConeChoiceFiber_hasInitial {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.universalConesOverProjection
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
            _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
            _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X) x) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  let q := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.universalConesOverProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X
  have he : (loopConeChoiceIso X).hom ≫ q = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X := by
    rw [← Category.assoc, loopConeChoiceIso_diagram]
    rfl
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) q (loopConeChoiceIso X).hom he x
  have : IsIso f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberMap_isIso _ _ _ _ _
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiber_hasInitial_of_loopEquivalence s hs hΩ x
  exact ⟨f.app (Opposite.op ⦋0⦌) v, hv.map_of_isIso f⟩
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
