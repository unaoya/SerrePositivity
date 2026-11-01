module

public import SerrePositivity.InfinityCategories.F1B.Localization.AdjointLocalization
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

/-!
概要：反射射影が反転する辺を反転する関手を、元の単位で射影に沿って分解する。
方針：単位の指定ホモトピーを後合成し、各成分の可逆性を関手同型にする。
規約：元の単位の像の類を保持。使われ方：普遍差への比較の第一射影の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.AdjointLocalization
variable {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) [IsIso a.counit]
  (T : X ⟶ Z) (hT : InvertsEdges T (invertedEdges F))

def factorIso : FunctorIso T ((F ≫ G) ≫ T) := by
  let H := functorHomotopyPostcomp (functorHomHomotopy a.unitHom) T
  have hi : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
    intro x
    exact (isInvertibleEdge_congr (e := (edgeOfSimplex
      (simplicialHomotopyVertexEdge (functorHomHomotopy a.unitHom) x).edge).map
        ((truncation 2).map T))
      (f := (simplicialHomotopyVertexEdge H x).toTruncated) rfl).mp
        (hT (unitComponent_mem_invertedEdges a x))
  have hm : IsIso ((hoFunctor.map ((ihom X).map T)).toFunctor.map a.unitHom) := by
    have h := functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H hi
    change IsIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) at h
    rwa [functorHomotopyPostcomp_hom, functorHomHomotopy_hom] at h
  exact (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
    (Category.id_comp T).symm)) ≪≫
      asIso ((hoFunctor.map ((ihom X).map T)).toFunctor.map a.unitHom)

lemma factorIso_hom_arrow : Arrow.mk (factorIso a T hT).hom =
    Arrow.mk ((hoFunctor.map ((ihom X).map T)).toFunctor.map a.unitHom) := by
  simp only [factorIso, Iso.trans_hom, eqToIso.hom, asIso_hom]
  exact arrow_mk_eqToHom_comp _ _

end SerrePositivity.KST.LocalizingInvariants.AdjointLocalization
