module

public import SerrePositivity.KST.Spectra.PointedPathProjectionContraction
public import SerrePositivity.KST.Spectra.PointedVerticalPathFiber
public import SerrePositivity.KST.Spectra.LoopTraceContraction

/-!
概要：同じ射影を持つ二端点の構造区間を、元の射影区間そのものを持つ loop 単体へ移す。
方針：零次族の厳密式で両端を照合し、類の恒等性から同じ区間の収縮を回収する。
規約：収縮の回収には底の Kan 性を使う。使われ方：非零境界の構造比較の収縮条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping
variable {T E B : PointedSimplicialSet.{u}} (p : E ⟶ B) {f g : T ⟶ E}
  (P : VerticalPath (PointedObject.toPoint E) f g) (he : g ≫ p = f ≫ p)

/-- 元の射影区間をそのまま持つ、同じ射影頂点での loop 単体。 -/
def projectionLoop : (PointedObject.basedHom T B).right.PtSimplex 1 (familyVertex (f ≫ p)) where
  map := P.path ≫ (PointedObject.basedHomMap T p).right
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, SSet.comp_const]
    fin_cases j
    · change stdSimplex.δ (0 : Fin 2) ≫
        (P.path ≫ (PointedObject.basedHomMap T p).right) = SSet.const (familyVertex (f ≫ p))
      rw [← Category.assoc, P.one, pointFamily_post, he, pointFamily_eq_const]
    · change stdSimplex.δ (1 : Fin 2) ≫
        (P.path ≫ (PointedObject.basedHomMap T p).right) = SSet.const (familyVertex (f ≫ p))
      rw [← Category.assoc, P.zero, pointFamily_post, pointFamily_eq_const]

/-- 射影 loop の類が恒等射なら、元の射影区間を両端点固定で実際に収縮できる。 -/
lemma exists_projection_contraction_of_trace_identity [KanComplex B.right]
    (h : SSet.HomotopyCategory.homMk (FundamentalLoop.edge (projectionLoop p P he)) =
      𝟙 (SSet.HomotopyCategory.mk (familyVertex (f ≫ p)))) :
    ∃ K : SSet.Homotopy (P.path ≫ (PointedObject.basedHomMap T p).right)
        (SSet.const (familyVertex (f ≫ p))),
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ K.h =
        fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path ≫
          (PointedObject.basedHomMap T p).right := by
  let homKan : KanComplex (PointedObject.basedHom T B).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact exists_loop_contraction_of_homMk_eq_id (projectionLoop p P he) h

/-- 射影 loop の恒等性は、元の構造区間を同じ端点を固定して垂直化できることと同値。 -/
lemma trace_identity_iff_vertical_deformation [KanComplex B.right]
    (hp : SSet.modelCategoryQuillen.J.rlp p.right) :
    (SSet.HomotopyCategory.homMk (FundamentalLoop.edge (projectionLoop p P he)) =
      𝟙 (SSet.HomotopyCategory.mk (familyVertex (f ≫ p)))) ↔
    (∃ Q : VerticalPath p f g, ∃ V : SSet.Homotopy P.path Q.path,
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path) := by
  let homKan : KanComplex (PointedObject.basedHom T B).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  constructor
  · intro h
    exact (projection_contraction_iff_vertical_deformation p hp P).1
      (exists_projection_contraction_of_trace_identity p P he h)
  · intro h
    obtain ⟨K, hb⟩ := (projection_contraction_iff_vertical_deformation p hp P).2 h
    exact homMk_eq_id_of_loop_contraction (projectionLoop p P he) K hb

end SerrePositivity.KST.Spectra.PointedMapping
