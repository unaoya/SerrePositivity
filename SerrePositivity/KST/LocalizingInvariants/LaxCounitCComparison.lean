module

public import SerrePositivity.KST.LocalizingInvariants.LaxCounitCofiberSecond
public import SerrePositivity.KST.LocalizingInvariants.LaxCAdjunction
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.RelativeBoundaryInvertibility
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：元の D 随伴余単位の cofiber 全族は、元の第一射影の後の C 包含と関手同型。
方針：第二射影が零である点で C 単位を反転し、その制限を点ごとの判定で可逆にする。
規約：同じ単位・余単位を使う。使われ方：一般商の二脚の coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma fromC_unit_component_isIso (x : (laxCategory p q).obj _⦋0⦌)
    (hz : IsZeroVertex ((laxSnd p q).hom.app (Opposite.op ⦋0⦌) x)) :
    IsIso (functorHomEvaluate (LaxInclusion.fromCAdjunction p q).unitHom x) := by
  let H := functorHomHomotopy (LaxInclusion.fromCAdjunction p q).unitHom
  let J := functorHomotopyPostcomp H (laxFst p q).hom
  have hj : IsIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J)) := by
    rw [functorHomotopyPostcomp_hom, functorHomHomotopy_hom]
    exact (LaxInclusion.fromCAdjunction p q).unit_postcompLeft_isIso
  have hm := homotopy_component_isInvertible_of_isIso J x
  have he : IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
    apply isInvertibleEdge_of_terminalBoundaries (laxFst p q).hom
      (simplicialHomotopyVertexEdge H x).toTruncated
    · exact lax_fst_terminalBoundary p.hom q.hom x hz.2
        (IsExactFunctor.preservesZero (F := q.hom) _ hz).2
    · exact LaxInclusion.fromC_terminalBoundary p q ((laxFst p q).hom.app _ x)
    · exact (isInvertibleEdge_congr
        (f := (simplicialHomotopyVertexEdge J x).toTruncated) rfl).mpr hm
  have hh := functorHomEvaluate_homotopy H x
  rw [functorHomHomotopy_hom] at hh
  exact hh.symm ▸ he

def cofiber_unitIso : FunctorIso (cofiber p q)
    ((cofiber p q ≫ (laxFst p q).hom) ≫ LaxInclusion.fromC p q) := by
  let α : FunctorHom (cofiber p q ≫ 𝟙 (laxCategory p q).obj)
      (cofiber p q ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) :=
    (hoFunctor.map ((pre (cofiber p q)).app (laxCategory p q).obj)).toFunctor.map
    (LaxInclusion.fromCAdjunction p q).unitHom
  let H := functorHomHomotopy α
  have hi : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
    apply functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
    intro x
    have he := functorHomEvaluate_homotopy H x
    rw [functorHomHomotopy_hom, functorHomEvaluate_precomp] at he
    change IsIso (Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge H x).toTruncated)
    exact he ▸ fromC_unit_component_isIso p q ((cofiber p q).app _ x) (cofiber_snd_zero p q x)
  have hα : IsIso α := by
    change IsIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) at hi
    rw [functorHomHomotopy_hom] at hi
    exact hi
  have e := asIso α
  change FunctorIso (cofiber p q)
    ((cofiber p q ≫ (laxFst p q).hom) ≫ LaxInclusion.fromC p q) at e
  exact e

def cofiber_fromCIso : FunctorIso (cofiber p q)
    ((laxFst p q).hom ≫ LaxInclusion.fromC p q) :=
  cofiber_unitIso p q ≪≫ FunctorIso.postcomp (cofiber_fstIso p q) (LaxInclusion.fromC p q)

end SerrePositivity.KST.LocalizingInvariants.LaxCounit
