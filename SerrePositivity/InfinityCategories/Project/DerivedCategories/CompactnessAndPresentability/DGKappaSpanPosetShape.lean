module
public import Mathlib.Tactic.DeriveFintype
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.SpanNerveHornIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.StrictSpanPointHomEnd
/-!
概要：実 cone の span 形状を、三対象の小さい poset の nerve と同定する。
方針：既存の span nerve とホーンの同型へ、同じ三対象・同じ比較関係の poset を接続する。
規約：全単体と宇宙持ち上げを保持し、単にホモトピー圏の形状へ置換しない。
使われ方：D-8 c4。P-9 の小さい poset 余極限の κ-compact 閉性を実 cone へ適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial


/-- 実 span の三頂点。対象宇宙 u の有限型として保持する。 -/
@[ext] structure DGKappaSpanPoset : Type u where
  val : Fin 3
  deriving DecidableEq

instance : Fintype DGKappaSpanPoset.{u} :=
  Fintype.ofEquiv (Fin 3) {
    toFun := DGKappaSpanPoset.mk
    invFun := DGKappaSpanPoset.val
    left_inv _ := rfl
    right_inv a := by cases a; rfl }

instance : PartialOrder DGKappaSpanPoset.{u} where
  le a b := a.val = 0 ∨ a.val = b.val
  le_refl _ := Or.inr rfl
  le_trans _ _ _ h k := h.elim Or.inl
    (fun e ↦ k.elim (fun h ↦ Or.inl (e.trans h)) (fun h ↦ Or.inr (e.trans h)))
  le_antisymm a b h k := by
    cases a with | mk a =>
      cases b with | mk b =>
        congr 1
        rcases h with h | h
        · rcases k with k | k
          · exact h.trans k.symm
          · exact k.symm
        · exact h

/-- 三対象 poset から既存の小さい span への、同じ頂点を保つ関手。 -/
def dgKappaSpanPosetToSpan : DGKappaSpanPoset.{u} ⥤ AsSmall.{u} WalkingSpan where
  obj a := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex a.val
  map {a b} f := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex_nonempty_hom a.val b.val (by
      rcases (leOfHom f : a.val = 0 ∨ a.val = b.val) with h | h
      · rw [h]; exact Fin.zero_le _
      · exact le_of_eq h) (by
      rcases (leOfHom f : a.val = 0 ∨ a.val = b.val) with h | h <;> omega)).some
  map_id _ := by apply ULift.ext; exact Subsingleton.elim _ _
  map_comp _ _ := by apply ULift.ext; exact Subsingleton.elim _ _

/-- 既存の小さい span から、同じ三頂点の poset への逆関手。 -/
def dgKappaSpanToPoset : AsSmall.{u} WalkingSpan ⥤ DGKappaSpanPoset.{u} where
  obj a := ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex a⟩
  map {a b} f := homOfLE (by
    change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex a = 0 ∨ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex a = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex b
    have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex_hom_condition f
    by_cases h0 : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex a = 0
    · exact Or.inl h0
    · right; apply Fin.ext; omega)

/-- 三対象 poset の nerve と既存の小さい span の nerve の厳密な同型。 -/
def dgKappaSpanPosetNerveIso : nerve DGKappaSpanPoset.{u} ≅
    nerve (AsSmall.{u} WalkingSpan) where
  hom := nerveMap dgKappaSpanPosetToSpan
  inv := nerveMap dgKappaSpanToPoset
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change (s ⋙ dgKappaSpanPosetToSpan) ⋙ dgKappaSpanToPoset = s
    have h : ∀ i, ((s ⋙ dgKappaSpanPosetToSpan) ⋙ dgKappaSpanToPoset).obj i = s.obj i := by
      intro i
      apply DGKappaSpanPoset.ext
      exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex_indexVertex (s.obj i).val
    exact ComposableArrows.ext h (fun _ _ ↦ Subsingleton.elim _ _)

  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change (s ⋙ dgKappaSpanToPoset) ⋙ dgKappaSpanPosetToSpan = s
    have h : ∀ i, ((s ⋙ dgKappaSpanToPoset) ⋙ dgKappaSpanPosetToSpan).obj i = s.obj i := by
      intro i
      exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex_vertexIndex (s.obj i)
    exact ComposableArrows.ext h (fun _ _ ↦ by apply ULift.ext; exact Subsingleton.elim _ _)

/-- 小さい poset 形状の持ち上げと、元の宇宙の実 span ホーンとの厳密な同型。 -/
def dgKappaSpanPosetHornIso :
    (SSet.uliftFunctor.{v, u}).obj (nerve DGKappaSpanPoset.{u}) ≅
      (horn 2 0 : SSet.{max u v}) :=
  (SSet.uliftFunctor.{v, u}).mapIso dgKappaSpanPosetNerveIso ≪≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanHornIso

end SerrePositivity.InfinityCategories.Project.DerivedCategories
