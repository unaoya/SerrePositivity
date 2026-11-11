module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsomorphismFiberZero
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquareComparisonIso

/-! # 指定実頂点の安定閉包と完全関手の零化

概要：零頂点・同型・実 cofiber/fiber で閉じる最小の頂点条件を構成する。
方針：有限の生成手順を帰納的に表し、完全関手の実四角形保存で零化を延長する。
規約：元の対象集合だけでなく安定閉包に沿う辺を局所化に使う。使われ方：β3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

/-- 指定頂点から零・実同型・全 cofiber/fiber により生成される安定な頂点条件。 -/
inductive StableVertexClosure {X : SSet.{u}} (P : Set (X _⦋0⦌)) : X _⦋0⦌ → Prop
  | of_mem {x} (hx : x ∈ P) : StableVertexClosure P x
  | of_zero {x} (hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) : StableVertexClosure P x
  | of_iso {x y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (hx : StableVertexClosure P x) : StableVertexClosure P y
  | of_cofiber (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
      (h₀ : StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0))
      (h₁ : StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0)) :
      StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1)
  | of_fiber (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t)
      (h₁ : StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0))
      (h₂ : StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1)) :
      StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)

/-- 完全関手が指定頂点を零化すると、その安定閉包の全頂点を零化する。 -/
lemma kills_stableVertexClosure {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
    (P : Set (X _⦋0⦌)) (h : ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x))
    {x : X _⦋0⦌} (hx : StableVertexClosure P x) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) := by
  induction hx with
  | of_mem hx => exact h _ hx
  | of_zero hx => exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F) _ hx
  | of_iso e _ ih => exact ih.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e F)
  | of_cofiber t ht _ _ ih₀ ih₁ =>
    let T := t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F))
    have hm : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence T := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht
    have hi : IsIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom T.square) :=
      isIso_of_isTerminal ih₀.2.isTerminalHo ih₁.2.isTerminalHo _
    exact T.zero_cofiber_of_isIso_bottom hm hi
  | of_fiber t ht _ _ ih₁ ih₂ =>
    let T := t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F))
    have hm : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence T := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesFiber F t ht
    let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ T.square))
    let s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f := {
      toZeroTriangle := T
      right_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
      isPullback := hm }
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow T.square) :=
      isIso_of_isTerminal ih₁.2.isTerminalHo ih₂.2.isTerminalHo _
    exact s.zero_of_homMk_isIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow T.square) (f := f)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge T.square)).mp hi)

/-- 安定閉包に沿う cofiber 辺の反転は、元の指定頂点の零化と同値。 -/
theorem inverts_stableVertexClosureEdges_iff_kills
    {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] (P : Set (X _⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | StableVertexClosure P x}) ↔
      ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.inverts_cofiberLocalizingEdges_iff_kills]
  exact ⟨fun h x hx => h x (StableVertexClosure.of_mem hx),
    fun h x hx => kills_stableVertexClosure F P h hx⟩

/-- 安定閉包で定まる辺の所属は、任意に選んだ実 cofiber で判定できる。 -/
lemma cofiberStableEdges_mem_iff {X : SSet.{u}} [Quasicategory X]
    (P : Set (X _⦋0⦌)) {a : X _⦋1⦌} (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)) :
    a ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | StableVertexClosure P x} ↔
      StableVertexClosure P s.cofiber := by
  constructor
  · rintro ⟨r, z, hz, ⟨e⟩⟩
    exact StableVertexClosure.of_iso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquareComparisonIso r s)
      (StableVertexClosure.of_iso e.symm hz)
  · intro hs
    exact ⟨s, s.cofiber, hs, ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
