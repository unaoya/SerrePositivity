module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy

/-!
概要：Kan 複体への射のホモトピー類と写像空間の連結成分。
方針：辺の同値閉包をホモトピー圏の同型に送り、その代表辺を uncurry する。
規約：始域の Kan 性は不要。標的の Kan 性により全ての辺が可逆。
使われ方：Kerodon §3.1.7（Tag 00U1）、弱ホモトピー同値の Kan 複体での判定。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：Kan 複体の同じ連結成分の二頂点はホモトピー圏で同型。
方針：辺の同値閉包に沿って可逆な辺の類を合成する。
規約：同型は頂点の等式を意味しない。
使われ方：写像空間の π₀ の等式から実際のホモトピーを回収する。 -/
lemma nonempty_vertexIso_of_piZero_eq {K : SSet.{u}} [KanComplex K]
    {x y : K _⦋0⦌} (h : SSet.π₀.mk x = SSet.π₀.mk y) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) := by
  have he := (SSet.π₀.mk_eq_mk_iff x y).mp h
  clear h
  induction he with
  | rel a b h =>
    obtain ⟨e⟩ := h
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) :=
      IsGroupoid.all_isIso (C := hoFunctor.obj K) _
    exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)⟩
  | refl a => exact ⟨Iso.refl _⟩
  | symm a b h ih => exact ih.map Iso.symm
  | trans a b c h k ih ik =>
    obtain ⟨e⟩ := ih
    obtain ⟨f⟩ := ik
    exact ⟨e ≪≫ f⟩

/-- 概要：Kan 標的への射の写像空間の連結成分の等式は実際のホモトピーと同値。
方針：同じ成分から関手の同型を得て代表辺を uncurry する。逆はホモトピーの頂点辺。
規約：A は任意の単体集合で、Z にだけ Kan 性を要求する。
使われ方：Kerodon §3.1.7（Tag 00U1） のホモトピー類の定義との一致。 -/
lemma functorVertex_piZero_eq_iff_homotopy {A Z : SSet.{u}} [KanComplex Z]
    (f g : A ⟶ Z) :
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) = SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) ↔
      Nonempty (SSet.Homotopy f g) := by
  constructor
  · intro h
    obtain ⟨e⟩ := nonempty_vertexIso_of_piZero_eq h
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy e⟩
  · rintro ⟨H⟩
    exact SSet.π₀.sound (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
