module
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingEdges
public import SerrePositivity.InfinityCategories.Stable.IsomorphismFiberZero
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso

/-! # 指定実頂点の安定閉包と完全関手の零化

概要：零頂点・同型・実 cofiber/fiber で閉じる最小の頂点条件を構成する。
方針：有限の生成手順を帰納的に表し、完全関手の実四角形保存で零化を延長する。
規約：元の対象集合だけでなく安定閉包に沿う辺を局所化に使う。使われ方：β3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial

/-- 指定頂点から零・実同型・全 cofiber/fiber により生成される安定な頂点条件。 -/
inductive StableVertexClosure {X : SSet.{u}} (P : Set (X _⦋0⦌)) : X _⦋0⦌ → Prop
  | of_mem {x} (hx : x ∈ P) : StableVertexClosure P x
  | of_zero {x} (hx : IsZeroVertex x) : StableVertexClosure P x
  | of_iso {x y} (e : VertexIso x y) (hx : StableVertexClosure P x) : StableVertexClosure P y
  | of_cofiber (t : ZeroTriangle X) (ht : IsCofiberSequence t)
      (h₀ : StableVertexClosure P (squareVertex t.square 0 0))
      (h₁ : StableVertexClosure P (squareVertex t.square 1 0)) :
      StableVertexClosure P (squareVertex t.square 1 1)
  | of_fiber (t : ZeroTriangle X) (ht : IsFiberSequence t)
      (h₁ : StableVertexClosure P (squareVertex t.square 1 0))
      (h₂ : StableVertexClosure P (squareVertex t.square 1 1)) :
      StableVertexClosure P (squareVertex t.square 0 0)

/-- 完全関手が指定頂点を零化すると、その安定閉包の全頂点を零化する。 -/
lemma kills_stableVertexClosure {X Y : SSet.{u}} [Quasicategory X] [IsStable X]
    [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]
    (P : Set (X _⦋0⦌)) (h : ∀ x ∈ P, IsZeroVertex (F.app (Opposite.op ⦋0⦌) x))
    {x : X _⦋0⦌} (hx : StableVertexClosure P x) :
    IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) := by
  induction hx with
  | of_mem hx => exact h _ hx
  | of_zero hx => exact IsExactFunctor.preservesZero (F := F) _ hx
  | of_iso e _ ih => exact ih.of_vertexIso (VertexIso.map e F)
  | of_cofiber t ht _ _ ih₀ ih₁ =>
    let T := t.map F (IsExactFunctor.preservesZero (F := F))
    have hm : IsCofiberSequence T := IsExactFunctor.preservesCofiber (F := F) t ht
    have hi : IsIso (squareHoBottom T.square) :=
      isIso_of_isTerminal ih₀.2.isTerminalHo ih₁.2.isTerminalHo _
    exact T.zero_cofiber_of_isIso_bottom hm hi
  | of_fiber t ht _ _ ih₁ ih₂ =>
    let T := t.map F (IsExactFunctor.preservesZero (F := F))
    have hm : IsFiberSequence T := IsExactFunctor.preservesFiber F t ht
    let f := edgeOfSimplex (SSet.yonedaEquiv (squareRightEdge ≫ T.square))
    let s : FiberSquare f := {
      toZeroTriangle := T
      right_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
      isPullback := hm }
    have hi : IsInvertibleEdge (squareRightArrow T.square) :=
      isIso_of_isTerminal ih₁.2.isTerminalHo ih₂.2.isTerminalHo _
    exact s.zero_of_homMk_isIso
      ((isInvertibleEdge_congr (e := squareRightArrow T.square) (f := f)
        (squareRightArrow_edge T.square)).mp hi)

/-- 安定閉包に沿う cofiber 辺の反転は、元の指定頂点の零化と同値。 -/
theorem inverts_stableVertexClosureEdges_iff_kills
    {X Y : SSet.{u}} [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] (P : Set (X _⦋0⦌)) :
    InvertsEdges F (cofiberLocalizingEdges {x | StableVertexClosure P x}) ↔
      ∀ x ∈ P, IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) := by
  rw [inverts_cofiberLocalizingEdges_iff_kills]
  exact ⟨fun h x hx => h x (StableVertexClosure.of_mem hx),
    fun h x hx => kills_stableVertexClosure F P h hx⟩

/-- 安定閉包で定まる辺の所属は、任意に選んだ実 cofiber で判定できる。 -/
lemma cofiberStableEdges_mem_iff {X : SSet.{u}} [Quasicategory X]
    (P : Set (X _⦋0⦌)) {a : X _⦋1⦌} (s : CofiberSquare (edgeOfSimplex a)) :
    a ∈ cofiberLocalizingEdges {x | StableVertexClosure P x} ↔
      StableVertexClosure P s.cofiber := by
  constructor
  · rintro ⟨r, z, hz, ⟨e⟩⟩
    exact StableVertexClosure.of_iso (cofiberSquareComparisonIso r s)
      (StableVertexClosure.of_iso e.symm hz)
  · intro hs
    exact ⟨s, s.cofiber, hs, ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories
