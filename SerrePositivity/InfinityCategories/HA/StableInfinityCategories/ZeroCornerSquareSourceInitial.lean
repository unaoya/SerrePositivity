module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroOuterConeSourceInitial

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

/-- 同じ固定頂点を保つ錐の比較 `coneInputFullSubcomplexIso_hom_fst`。 -/
lemma coneInputFullSubcomplexIso_hom_fst {E B : SSet.{u}} (f : E ⟶ B)
    (Q : B _⦋0⦌ → Prop) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneInputFullSubcomplexIso f Q).hom ≫ pullback.fst f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B Q).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E (fun v ↦ Q (f.app (Opposite.op ⦋0⦌) v))).ι :=
  pullback.lift_fst _ _ _

/-- 同じ固定頂点を保つ錐の比較 `zeroCornerSquareConeIso_diagram`。 -/
lemma zeroCornerSquareConeIso_diagram (X : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).hom ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso X).hom := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso, Iso.trans_hom]
  rw [Category.assoc, coneInputFullSubcomplexIso_hom_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso_hom_ι]

/-- 同じ固定頂点を保つ錐の比較 `squareConeFunctorIso_apex`。 -/
lemma squareConeFunctorIso_apex (X : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso X).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation]
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  have hp := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_initialPoint.{u}
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u})).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = _ at hp
  rw [hp]
  rfl

/-- 同じ固定頂点を保つ錐の比較 `zeroCornerSquareSource`。 -/
def zeroCornerSquareSource (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquares X ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex).ι ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 同じ固定頂点を保つ錐の比較 `zeroCornerSquareConeIso_source`。 -/
lemma zeroCornerSquareConeIso_source (X : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).hom ≫
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X) =
      zeroCornerSquareSource X := by
  rw [← Category.assoc, zeroCornerSquareConeIso_diagram, Category.assoc,
    squareConeFunctorIso_apex]
  rfl

/-- 同じ固定頂点を保つ錐の比較 `zeroCornerSquareSourceFiber_hasInitial`。 -/
lemma zeroCornerSquareSourceFiber_hasInitial {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (zeroCornerSquareSource X) x) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  let q := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (zeroCornerSquareSource X) q (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).hom
    (zeroCornerSquareConeIso_source X) x
  have : IsIso f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberMap_isIso _ _ _ _ _
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterConeSourceFiber_hasInitial s hs hΩ x
  have ht := hv.map_of_isIso (inv f)
  exact ⟨(inv f).app (Opposite.op ⦋0⦌) v, ht⟩
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
