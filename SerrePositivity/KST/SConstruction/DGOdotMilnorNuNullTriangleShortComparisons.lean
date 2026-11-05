module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullLowerPrismSides
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullUpperPrismSides
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerHom

/-!
概要：元上下二胞体の全関手同型から、元四辺の指定全比較をそのまま回収する。
方針：同じ実ホモトピーの短辺制限をホモトピー圏へ写し、元端点等号で輸送する。
規約：同型の存在だけでなく元の指定同型そのものを保持する。
使われ方：元四角形全比較の指定境界に必要な四つの短辺回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma nullTriangleShortComparison
    {f g : (Δ[2] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u + 1}}
    {f' g' : (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u + 1}}
    (H : SSet.Homotopy f g) (e : FunctorIso f g)
    (he : e.hom = Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))
    (q : (Δ[1] : SSet.{u + 2}) ⟶ Δ[2]) (hf : q ≫ f = f') (hg : q ≫ g = g')
    (H' : SSet.Homotopy f' g') (e' : FunctorIso f' g')
    (he' : e'.hom = Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H'))
    (hh : (q ▷ (Δ[1] : SSet.{u + 2})) ≫ H.h = H'.h) :
    F2.functorIsoOfEq (e.precomp q) hf hg = e' := by
  subst f' g'
  change e.precomp q = e'
  apply Iso.ext
  rw [F2.functorIso_precomp_hom, he, he']
  change Truncated.HomotopyCategory.homMk
    ((functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map ((pre q).app _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u + 1}))) =
        Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H')
  have hedge : (functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map ((pre q).app _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u + 1})) =
        functorEdgeOfSimplicialHomotopy H' := by
    apply Truncated.Edge.ext
    change ((pre q).app _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u + 1}).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry H.h)) = SSet.yonedaEquiv (curry H'.h)
    rw [← SSet.yonedaEquiv_comp, curry_pre_app, hh]
  exact congrArg Truncated.HomotopyCategory.homMk hedge

variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)

/-- 概要：元下全比較の短辺制限は同じ元包含の指定全比較そのもの。
方針：元短辺ホモトピーの厳密回収と同じ元二端点等号を使う。
規約：元指定同型の等号。使われ方：元全図式比較の指定短辺境界。 -/
lemma dgOdotMilnorNuNullLowerTriangleComparison_inclusion :
    F2.functorIsoOfEq
      ((dgOdotMilnorNuNullLowerTriangleComparison R d h).precomp
        (stdSimplex.δ (2 : Fin 3)))
      (dgOdotMilnorNuNullPrismTriangle_first_actual R d 1)
      (dgOdotMilnorNuNullPrismTriangle_first_absolute R d h 1) =
        dgOdotMilnorNuInclusionDiagramComparison R d h := by
  exact nullTriangleShortComparison (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)
    (dgOdotMilnorNuNullLowerTriangleComparison R d h) rfl (stdSimplex.δ (2 : Fin 3))
    (dgOdotMilnorNuNullPrismTriangle_first_actual R d 1)
    (dgOdotMilnorNuNullPrismTriangle_first_absolute R d h 1)
    (dgOdotMilnorNuInclusionDiagramHomotopy R d h)
    (dgOdotMilnorNuInclusionDiagramComparison R d h)
    (dgOdotMilnorNuInclusionDiagramHomotopy_comparison R d h).symm
    (dgOdotMilnorNuNullLowerTriangleHomotopy_face R d h 2 (by decide))

/-- 概要：元下全比較の短辺制限は同じ元商の指定全比較そのもの。
方針：元短辺ホモトピーの厳密回収と同じ元二端点等号を使う。
規約：元指定同型の等号。使われ方：元全図式比較の指定短辺境界。 -/
lemma dgOdotMilnorNuNullLowerTriangleComparison_projection :
    F2.functorIsoOfEq
      ((dgOdotMilnorNuNullLowerTriangleComparison R d h).precomp
        (stdSimplex.δ (0 : Fin 3)))
      (dgOdotMilnorNuNullPrismTriangle_last_actual R d 1)
      (dgOdotMilnorNuNullPrismTriangle_last_absolute R d h 1) =
        dgOdotMilnorNuProjectionDiagramComparison R d h := by
  exact nullTriangleShortComparison (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)
    (dgOdotMilnorNuNullLowerTriangleComparison R d h) rfl (stdSimplex.δ (0 : Fin 3))
    (dgOdotMilnorNuNullPrismTriangle_last_actual R d 1)
    (dgOdotMilnorNuNullPrismTriangle_last_absolute R d h 1)
    (dgOdotMilnorNuProjectionDiagramHomotopy R d h)
    (dgOdotMilnorNuProjectionDiagramComparison R d h)
    (dgOdotMilnorNuProjectionDiagramHomotopy_comparison R d h).symm
    (dgOdotMilnorNuNullLowerTriangleHomotopy_face R d h 0 (by decide))

/-- 概要：元上全比較の短辺制限は同じ元零角左辺の指定全比較そのもの。
方針：元短辺ホモトピーの厳密回収と同じ元二端点等号を使う。
規約：元指定同型の等号。使われ方：元全図式比較の指定短辺境界。 -/
lemma dgOdotMilnorNuNullUpperTriangleComparison_zeroLeft :
    F2.functorIsoOfEq
      ((dgOdotMilnorNuNullUpperTriangleComparison R d h).precomp
        (stdSimplex.δ (2 : Fin 3)))
      (dgOdotMilnorNuNullPrismTriangle_first_actual R d 0)
      (dgOdotMilnorNuNullPrismTriangle_first_absolute R d h 0) =
        dgOdotMilnorNuZeroLeftDiagramComparison R d h := by
  exact nullTriangleShortComparison (dgOdotMilnorNuNullUpperTriangleHomotopy R d h)
    (dgOdotMilnorNuNullUpperTriangleComparison R d h) rfl (stdSimplex.δ (2 : Fin 3))
    (dgOdotMilnorNuNullPrismTriangle_first_actual R d 0)
    (dgOdotMilnorNuNullPrismTriangle_first_absolute R d h 0)
    (dgOdotMilnorNuZeroLeftDiagramHomotopy R d h)
    (dgOdotMilnorNuZeroLeftDiagramComparison R d h)
    (dgOdotMilnorNuZeroLeftDiagramHomotopy_comparison R d h).symm
    (dgOdotMilnorNuNullUpperTriangleHomotopy_face R d h 2 (by decide))

/-- 概要：元上全比較の短辺制限は同じ元零角上辺の指定全比較そのもの。
方針：元短辺ホモトピーの厳密回収と同じ元二端点等号を使う。
規約：元指定同型の等号。使われ方：元全図式比較の指定短辺境界。 -/
lemma dgOdotMilnorNuNullUpperTriangleComparison_zeroTop :
    F2.functorIsoOfEq
      ((dgOdotMilnorNuNullUpperTriangleComparison R d h).precomp
        (stdSimplex.δ (0 : Fin 3)))
      (dgOdotMilnorNuNullPrismTriangle_last_actual R d 0)
      (dgOdotMilnorNuNullPrismTriangle_last_absolute R d h 0) =
        dgOdotMilnorNuZeroTopDiagramComparison R d h := by
  exact nullTriangleShortComparison (dgOdotMilnorNuNullUpperTriangleHomotopy R d h)
    (dgOdotMilnorNuNullUpperTriangleComparison R d h) rfl (stdSimplex.δ (0 : Fin 3))
    (dgOdotMilnorNuNullPrismTriangle_last_actual R d 0)
    (dgOdotMilnorNuNullPrismTriangle_last_absolute R d h 0)
    (dgOdotMilnorNuZeroTopDiagramHomotopy R d h)
    (dgOdotMilnorNuZeroTopDiagramComparison R d h)
    (dgOdotMilnorNuZeroTopDiagramHomotopy_comparison R d h).symm
    (dgOdotMilnorNuNullUpperTriangleHomotopy_face R d h 0 (by decide))

end SerrePositivity.KST.SConstruction
