module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseInitialTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeUnitHom

/-!
概要：全零完全関手の固定端点区間 Hom では、自己比較の射の類が一意となる。
方針：完全関手圏の終対象全成分を coherent 区間 Hom 比較へ充満忠実に写す。
規約：元の完全関手・元の区間を保持。自然な収縮を追加入力にしない。
使われ方：恒等実右面の上下比較の共有対角を同じ全比較へ合わせる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
local instance zeroIntervalStableHomKan : ∀ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_sHom_kanComplex X Y
variable (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
local instance zeroIntervalLiftedStableHomKan : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B)) := by
  letI : KanComplex (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_sHom_kanComplex A B
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_uliftFunctor_obj _

private abbrev zeroIntervalComponent : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B))
    (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x.down.val)

private def zeroIntervalComponentIso
    (h : ∃ x : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) : SSet.{u}) ≅
      zeroIntervalComponent A B := by
  let X := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) : SSet.{u})
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices_isContractibleKan h
  letI : KanComplex X := hc.kanComplex
  let j : X ⟶ SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι
      (fun s => by
        have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s) :=
          IsGroupoid.all_isIso (C := hoFunctor.obj X) _
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (by rfl)).mp
          (hs.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι))
  refine {
    hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((SSet.uliftFunctor.{u + 1, u}).map j)
      (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x.down)
    inv := {
      app n := ↾fun x => ULift.up ⟨x.val.down.val, fun α => x.property α⟩
      naturality n m α := by
        apply ConcreteCategory.hom_ext
        intro x
        apply ULift.ext
        apply Subtype.ext
        rfl }
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    rfl

private lemma zeroIntervalComponent_contractible
    (h : ∃ x : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (zeroIntervalComponent A B) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (zeroIntervalComponentIso A B h)
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices_isContractibleKan h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_nonempty_of_all_terminal
  · exact ⟨ULift.up (Classical.choice hc.nonempty)⟩
  · intro x
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isTerminalVertex_iff_ulift x.down).mp (hc.isTerminalVertex x.down)

/-- 概要：元全零完全関手の同じ固定端点区間 Hom の自己射の類は一意。
方針：元終対象成分の可縮性と全 Hom 比較の充満忠実性を使う。
規約：両端固定の全自己比較。使われ方：上下比較の対角の類の一致への還元。 -/
lemma stableZeroInterval_hom_ext (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hF : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x))
    (f g : SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F))) : f = g := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv A B F) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _ (fun x => (hF x).2)
  let z : (zeroIntervalComponent A B) _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.fullSubcomplexVertexEquiv _
    ⟨ULift.up (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B F), ht⟩
  let M : zeroIntervalComponent A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex B) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B))
      (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x.down.val)).ι ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B
  have hc := zeroIntervalComponent_contractible A B ⟨_, ht⟩
  letI : KanComplex (zeroIntervalComponent A B) := hc.kanComplex
  have hM : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful M := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_isQCatEquivalence (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B).isFullyFaithful
  have hz : M.app (Opposite.op ⦋0⦌) z = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F) := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B).app _
      (ULift.up (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B F)) = _
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B F)
    exact he.trans (congrArg
      (fun K : (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) ⟶ (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) =>
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) K))
      (Equiv.symm_apply_apply
        (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B) F))
  have hs : Subsingleton (SSet.HomotopyCategory.mk (M.app (Opposite.op ⦋0⦌) z) ⟶
      SSet.HomotopyCategory.mk (M.app (Opposite.op ⦋0⦌) z)) := by
    constructor
    intro a b
    have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.homotopyCategoryMap_bijective hM z z
    obtain ⟨a', ha⟩ := hb.2 a
    obtain ⟨b', hb⟩ := hb.2 b
    exact ha.symm.trans ((congrArg ((hoFunctor.map M).toFunctor.map)
      ((hc.isTerminalVertex z).isTerminalHo.hom_ext a' b')).trans hb)
  rw [hz] at hs
  exact hs.elim f g
end SerrePositivity.KST.SConstruction
