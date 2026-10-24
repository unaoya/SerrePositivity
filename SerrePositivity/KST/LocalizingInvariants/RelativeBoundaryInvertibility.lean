module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialBoundaryHom
public import SerrePositivity.InfinityCategories.Stable.TerminalBoundaryTransport

/-!
概要：同じ射影に相対的に始または終対象である両端の辺は、像の可逆性を反映する。
方針：指定 Hom の全単射で逆を持ち上げ、終対象の場合は反転する。
規約：射影全体の充満忠実性は不要。使われ方：lax 余単位 cofiber の C 単位の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma isInvertibleEdge_of_initialBoundaries {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y)
    (hx : InitialBoundaryLifting p x) (hy : InitialBoundaryLifting p y)
    (he : IsInvertibleEdge (e.map ((truncation 2).map p))) : IsInvertibleEdge e := by
  let F := (hoFunctor.map p).toFunctor
  let a := Truncated.HomotopyCategory.homMk e
  have ha : IsIso (F.map a) := he
  obtain ⟨b, hb⟩ := (SerrePositivity.InfinityCategories.F1B.hoFunctorMap_bijective_of_initialBoundary p y x hy).surjective
    (inv (F.map a))
  change IsIso a
  refine ⟨⟨b, ?_, ?_⟩⟩
  · apply (SerrePositivity.InfinityCategories.F1B.hoFunctorMap_bijective_of_initialBoundary p x x hx).injective
    change F.map (a ≫ b) = F.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, hb, CategoryTheory.Functor.map_id]
    exact IsIso.hom_inv_id _
  · apply (SerrePositivity.InfinityCategories.F1B.hoFunctorMap_bijective_of_initialBoundary p y y hy).injective
    change F.map (b ≫ a) = F.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, hb, CategoryTheory.Functor.map_id]
    exact IsIso.inv_hom_id _

lemma isInvertibleEdge_of_terminalBoundaries {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y)
    (hx : TerminalBoundaryLifting p x) (hy : TerminalBoundaryLifting p y)
    (he : IsInvertibleEdge (e.map ((truncation 2).map p))) : IsInvertibleEdge e := by
  apply (isInvertibleEdge_op_iff e).mp
  apply isInvertibleEdge_of_initialBoundaries (SSet.opFunctor.map p) (edgeOp e)
    hy.op_initial hx.op_initial
  exact (isInvertibleEdge_congr (X := Y.op) (e := (edgeOp e).map ((truncation 2).map
    (SSet.opFunctor.map p))) (f := edgeOp (e.map ((truncation 2).map p))) rfl).mpr he.op

end SerrePositivity.KST.LocalizingInvariants
