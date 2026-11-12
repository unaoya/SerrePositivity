module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberFunctorMapping
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberZeroSource
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-! # 指定対象の cofiber により定まる局所化の辺

概要：指定対象と同型な cofiber を持つ実辺のクラスを定義する。
方針：cofiber の選択を存在量化し、完全関手の零化条件と反転条件を比較する。
規約：局所化普遍性は仮定しない。使われ方：β3 の実 Verdier 商の反転条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 指定した実頂点と同型な cofiber を持つ実辺の集合。 -/
def cofiberLocalizingEdges {X : SSet.{u}} (P : Set (X _⦋0⦌)) : Set (X _⦋1⦌) :=
  {a | ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a),
    ∃ z ∈ P, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso s.cofiber z)}

variable {X Y : SSet.{u}} [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
variable (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] (P : Set (X _⦋0⦌))

/-- 完全関手は、零化する対象と同型な cofiber を持つ全ての辺を反転する。 -/
lemma inverts_cofiberLocalizingEdges_of_kills
    (h : ∀ z ∈ P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (cofiberLocalizingEdges P) := by
  rintro a ⟨s, z, hz, ⟨e⟩⟩
  apply (s.map_isInvertible_iff_zero F).2
  exact (h z hz).of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e F).symm

/-- 安定始域では、cofiber 辺を全て反転する完全関手は指定対象を全て零化する。 -/
lemma kills_of_inverts_cofiberLocalizingEdges [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (cofiberLocalizingEdges P)) :
    ∀ z ∈ P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) z) := by
  intro z hz
  let q := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X
  let f := Classical.choice (q.isInitial.nonempty_edge z)
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare f
  let e := s.cofiberIsoOfZeroSource q.isZero
  have hf : f.edge ∈ cofiberLocalizingEdges P := by
    let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex f.edge) := {
      toZeroTriangle := s.toZeroTriangle
      bottom_edge := s.bottom_edge
      isPushout := s.isPushout }
    exact ⟨t, z, hz, ⟨e⟩⟩
  have hi₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex f.edge).map ((truncation 2).map F)) := h hf
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (f.map ((truncation 2).map F)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex f.edge).map ((truncation 2).map F))
      (f := f.map ((truncation 2).map F)) rfl).mp hi₀
  exact ((s.map_isInvertible_iff_zero F).1 hi).of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e F)

/-- 導来対象の零化と cofiber 辺の反転は、完全関手について同値。 -/
theorem inverts_cofiberLocalizingEdges_iff_kills [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (cofiberLocalizingEdges P) ↔
      ∀ z ∈ P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) z) :=
  ⟨kills_of_inverts_cofiberLocalizingEdges F P, inverts_cofiberLocalizingEdges_of_kills F P⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
