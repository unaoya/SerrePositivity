module
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberBottomIsoTransport
public import SerrePositivity.InfinityCategories.Stable.CofiberFunctorMapping
/-!
概要：元の辺の像が全実辺を同型まで表示する完全関手に沿って、後続関手の完全性を反映する。
方針：一つの零対象と、元の各 cofiber の像から全錐の関手同型で任意 cofiber を比較する。
規約：対象・Arrow の Ho での全射だけでは済ませない。使われ方：Verdier 商からの延長関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
/-- 任意の実辺が、元の実辺の像と区間上の全関手圏で同型であるという条件。 -/
def HasArrowLiftsUpToIso {X Y : SSet.{u}} (q : X ⟶ Y) : Prop :=
  ∀ a : Y _⦋1⦌, ∃ b : X _⦋1⦌,
    Nonempty (FunctorIso (SSet.yonedaEquiv.symm b ≫ q) (SSet.yonedaEquiv.symm a))
/-- 実辺を同型まで覆う完全関手に沿う前合成は、後続の実関手の完全性を反映する。 -/
lemma isExactFunctor_of_precomp_arrowLifts {X Y Z : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [Quasicategory Z]
    (q : X ⟶ Y) [IsExactFunctor q] (hq : HasArrowLiftsUpToIso q)
    (G : Y ⟶ Z) [IsExactFunctor (q ≫ G)] : IsExactFunctor G where
  preservesZero y hy := by
    let z := chosenZeroVertex X
    have hzq := IsExactFunctor.preservesZero (F := q) z.vertex z.isZero
    have hzg := IsExactFunctor.preservesZero (F := q ≫ G) z.vertex z.isZero
    exact hzg.of_vertexIso (VertexIso.map (terminalVertexIso hzq.2 hy.2) G)
  preservesCofiber t ht := by
    let a := SSet.yonedaEquiv (squareBottomEdge ≫ t.square)
    obtain ⟨b, ⟨e⟩⟩ := hq a
    let f := edgeOfSimplex b
    let c := chosenCofiberSquare f
    let s := c.toZeroTriangle.map q (IsExactFunctor.preservesZero (F := q))
    have hs : IsCofiberSequence s := IsExactFunctor.preservesCofiber (F := q)
      c.toZeroTriangle c.isPushout
    have hb : squareBottomEdge ≫ s.square = SSet.yonedaEquiv.symm b ≫ q := by
      change squareBottomEdge ≫ (c.square ≫ q) = _
      rw [← Category.assoc, c.bottom_edge]
      rfl
    have ha : squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm a :=
      (SSet.yonedaEquiv.symm_apply_apply _).symm
    have he : FunctorIso (squareBottomEdge ≫ s.square) (squareBottomEdge ≫ t.square) :=
      (congrArg₂ (fun v w => FunctorIso v w) hb ha).mpr e
    obtain ⟨es⟩ := nonempty_cofiberSquareFunctorIso_of_bottom_iso s t hs ht he
    have hc : IsPushoutSquare (s.square ≫ G) := by
      have h := IsExactFunctor.preservesCofiber (F := q ≫ G) c.toZeroTriangle c.isPushout
      exact h
    exact hc.of_functorIso (FunctorIso.postcomp es G)
end SerrePositivity.InfinityCategories
