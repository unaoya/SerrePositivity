module

public import SerrePositivity.KST.LocalizingInvariants.LaxCounitCofiber
public import SerrePositivity.KST.LocalizingInvariants.AdjunctionCounitImage
public import SerrePositivity.InfinityCategories.Stable.CofiberFunctorMapping
public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveLocalization

/-!
概要：元の D 随伴余単位の cofiber は、第二射影で全て零となる。
方針：厳密な切断から可逆単位を得て余単位の第二射影を反転し、実 cofiber 判定を使う。
規約：同じ余単位の代表を保つ。使われ方：半直交 cofiber 全族と C 包含の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit

lemma ofHomotopy_vertex_edge {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (x : A _⦋0⦌) :
    intervalFunctorVertexEdge ((ZeroArrowFamily.ofHomotopy H).app (Opposite.op ⦋0⦌) x) =
      (simplicialHomotopyVertexEdge H x).edge := by
  rw [ZeroArrowFamily.ofHomotopy, intervalFunctorVertexEdge_curry]
  change H.h.app (Opposite.op ⦋1⦌)
    (PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
      H.h.app (Opposite.op ⦋1⦌)
        ((Truncated.Edge.id (X := (truncation 2).obj A) x).edge, homotopyIntervalEdge.edge)
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [pinchedConstant_one, hi]

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma counit_snd_isIso : IsIso ((hoFunctor.map ((ihom (laxCategory p q).obj).map
    (laxSnd p q).hom)).toFunctor.map (LaxInclusion.fromDAdjunction p q).counitHom) := by
  have : IsIso (LaxInclusion.fromDAdjunction p q).unitHom := by
    rw [LaxInclusion.fromDAdjunction_unit]
    infer_instance
  exact counit_postcompRight_isIso (LaxInclusion.fromDAdjunction p q)

lemma cofiber_snd_zero (x : (laxCategory p q).obj _⦋0⦌) :
    IsZeroVertex ((cofiber p q ≫ (laxSnd p q).hom).app (Opposite.op ⦋0⦌) x) := by
  let H := functorHomHomotopy (LaxInclusion.fromDAdjunction p q).counitHom
  let J := functorHomotopyPostcomp H (laxSnd p q).hom
  have hj : IsIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J)) := by
    rw [functorHomotopyPostcomp_hom, functorHomHomotopy_hom]
    exact counit_snd_isIso p q
  have hc := homotopy_component_isInvertible_of_isIso J x
  let s := CofiberFamily.cofiberSquareAt (laxCategory p q).obj (arrow p q) x
  have hi : IsInvertibleEdge ((edgeOfSimplex
      (intervalFunctorVertexEdge ((arrow p q).app (Opposite.op ⦋0⦌) x))).map
        ((truncation 2).map (laxSnd p q).hom)) := by
    apply (isInvertibleEdge_congr (f := (simplicialHomotopyVertexEdge J x).toTruncated) ?_).mpr hc
    change (laxSnd p q).hom.app (Opposite.op ⦋1⦌)
      (intervalFunctorVertexEdge ((ZeroArrowFamily.ofHomotopy H).app _ x)) =
        (laxSnd p q).hom.app (Opposite.op ⦋1⦌) (simplicialHomotopyVertexEdge H x).edge
    rw [ofHomotopy_vertex_edge]
  change IsZeroVertex ((laxSnd p q).hom.app (Opposite.op ⦋0⦌)
    ((CofiberFamily.cofiber (laxCategory p q).obj (arrow p q)).app _ x))
  rw [CofiberFamily.cofiber_vertex]
  exact (s.map_isInvertible_iff_zero (laxSnd p q).hom).mp hi

end SerrePositivity.KST.LocalizingInvariants.LaxCounit
