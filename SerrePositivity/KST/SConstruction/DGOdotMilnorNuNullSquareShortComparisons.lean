module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullSquareTriangleComparisons
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerComposition

/-!
概要：元全核面比較の包含辺・商辺制限は既存の指定全辺比較そのもの。
方針：元下全三角形比較の回収と元二短辺の指定比較を、前合成の結合で接続する。
規約：元指定同型の厳密等号を保持する。
使われ方：Sp 正本の核面の指定包含・商境界への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma nullSquarePrecompTwice {A B C X : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (p : B ⟶ A) (q : C ⟶ B) :
    HEq ((e.precomp p).precomp q) (e.precomp (q ≫ p)) := by
  have h : SSet.mapHomotopyCategory ((pre (q ≫ p)).app X) =
      SSet.mapHomotopyCategory ((pre p).app X) ⋙
        SSet.mapHomotopyCategory ((pre q).app X) := by
    change (hoFunctor.map ((pre (q ≫ p)).app X)).toFunctor = _
    rw [pre_map]
    change (hoFunctor.map ((pre p).app X ≫ (pre q).app X)).toFunctor = _
    rw [CategoryTheory.Functor.map_comp]
    rfl
  rw [F2.functorIso_precomp_eq_mapIso, F2.functorIso_precomp_eq_mapIso,
    F2.functorIso_precomp_eq_mapIso]
  exact (F2.mapIso_heq_of_functor_eq h e).symm

private lemma nullSquareShortFromTriangle {A B C X : SSet.{u}}
    {f g : A ⟶ X} {f' g' : B ⟶ X} {f'' g'' : C ⟶ X}
    (e : FunctorIso f g) (p : B ⟶ A) (q : C ⟶ B) (s : C ⟶ A)
    (hp : q ≫ p = s) (hf : p ≫ f = f') (hg : p ≫ g = g')
    (e' : FunctorIso f' g') (htri : F2.functorIsoOfEq (e.precomp p) hf hg = e')
    (hfs : q ≫ f' = f'') (hgs : q ≫ g' = g'')
    (e'' : FunctorIso f'' g'')
    (hshort : F2.functorIsoOfEq (e'.precomp q) hfs hgs = e'') :
    HEq (e.precomp s) e'' := by
  subst f' g'
  change e.precomp p = e' at htri
  subst e'
  have ht := nullSquarePrecompTwice e p q
  rw [hp] at ht
  exact ht.symm.trans ((F2.functorIsoOfEq_heq _ hfs hgs).symm.trans (heq_of_eq hshort))

private lemma nullSquareZeroCorner :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ squareLeftEdge =
      verdierZeroCorner := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i
    rfl

variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)

/-- 概要：元全核面比較の包含辺制限は同じ元指定包含比較。
方針：元下二胞体の全比較と元短辺比較の二回の厳密回収を接続する。
規約：指定全同型そのもの。使われ方：Sp の指定包含境界。 -/
lemma dgOdotMilnorNuNullSquareComparison_inclusion :
    (dgOdotMilnorNuNullSquareComparison R d h).precomp squareBottomEdge =
      dgOdotMilnorNuInclusionDiagramComparison R d h := by
  apply eq_of_heq
  exact nullSquareShortFromTriangle (dgOdotMilnorNuNullSquareComparison R d h)
    (squareTriangle 1) (stdSimplex.δ (2 : Fin 3)) squareBottomEdge
    stableSquareTriangle_bottomEdge _ _ (dgOdotMilnorNuNullLowerTriangleComparison R d h)
    (dgOdotMilnorNuNullSquareComparison_lower R d h) _ _
    (dgOdotMilnorNuInclusionDiagramComparison R d h)
    (dgOdotMilnorNuNullLowerTriangleComparison_inclusion R d h)

/-- 概要：元全核面比較の商辺制限は同じ元指定射影比較。
方針：元下二胞体の全比較と同じ元商辺比較を前合成の結合で接続する。
規約：指定全同型そのもの。使われ方：Sp の指定商境界。 -/
lemma dgOdotMilnorNuNullSquareComparison_projection :
    (dgOdotMilnorNuNullSquareComparison R d h).precomp squareRightEdge =
      dgOdotMilnorNuProjectionDiagramComparison R d h := by
  apply eq_of_heq
  exact nullSquareShortFromTriangle (dgOdotMilnorNuNullSquareComparison R d h)
    (squareTriangle 1) (stdSimplex.δ (0 : Fin 3)) squareRightEdge
    squareTriangle_rightEdge _ _ (dgOdotMilnorNuNullLowerTriangleComparison R d h)
    (dgOdotMilnorNuNullSquareComparison_lower R d h) _ _
    (dgOdotMilnorNuProjectionDiagramComparison R d h)
    (dgOdotMilnorNuNullLowerTriangleComparison_projection R d h)

/-- 概要：元全核面比較の零角左辺制限は同じ元指定全比較。
方針：元上二胞体の全比較と同じ元短辺比較を前合成の結合で接続する。
規約：指定全同型そのもの。使われ方：元零角境界の厳密回収。 -/
lemma dgOdotMilnorNuNullSquareComparison_zeroLeft :
    (dgOdotMilnorNuNullSquareComparison R d h).precomp squareLeftEdge =
      dgOdotMilnorNuZeroLeftDiagramComparison R d h := by
  apply eq_of_heq
  exact nullSquareShortFromTriangle (dgOdotMilnorNuNullSquareComparison R d h)
    (squareTriangle 0) (stdSimplex.δ (2 : Fin 3)) squareLeftEdge
    stableSquareTriangle_leftEdge _ _ (dgOdotMilnorNuNullUpperTriangleComparison R d h)
    (dgOdotMilnorNuNullSquareComparison_upper R d h) _ _
    (dgOdotMilnorNuZeroLeftDiagramComparison R d h)
    (dgOdotMilnorNuNullUpperTriangleComparison_zeroLeft R d h)

/-- 概要：元全核面比較の零角上辺制限は同じ元指定全比較。
方針：元上二胞体の全比較と同じ元短辺比較を前合成の結合で接続する。
規約：指定全同型そのもの。使われ方：元零角境界の厳密回収。 -/
lemma dgOdotMilnorNuNullSquareComparison_zeroTop :
    (dgOdotMilnorNuNullSquareComparison R d h).precomp squareTopEdge =
      dgOdotMilnorNuZeroTopDiagramComparison R d h := by
  apply eq_of_heq
  exact nullSquareShortFromTriangle (dgOdotMilnorNuNullSquareComparison R d h)
    (squareTriangle 0) (stdSimplex.δ (0 : Fin 3)) squareTopEdge
    squareTriangle_topEdge _ _ (dgOdotMilnorNuNullUpperTriangleComparison R d h)
    (dgOdotMilnorNuNullSquareComparison_upper R d h) _ _
    (dgOdotMilnorNuZeroTopDiagramComparison R d h)
    (dgOdotMilnorNuNullUpperTriangleComparison_zeroTop R d h)

/-- 概要：元指定零角左辺比較の零角端点を、元核四角形の指定零角比較として保持する。
方針：同じ元指定全辺比較を元の零角頂点へ制限する。
規約：全四角形比較から選ばない。使われ方：Sp の指定三境界の零角入力。 -/
def dgOdotMilnorNuNullRawSquareZeroBoundary : FunctorIso
    (verdierZeroCorner ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (verdierZeroCorner ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  F2.functorIsoOfEq
    ((dgOdotMilnorNuZeroLeftDiagramComparison R d h).precomp (stdSimplex.δ (0 : Fin 2)))
    (by rw [← Category.assoc, nullSquareZeroCorner])
    (by rw [← Category.assoc, nullSquareZeroCorner])

/-- 概要：元全核面比較の零角制限は同じ元指定零角比較そのもの。
方針：元零角左辺の全比較と同じ元端点への制限を接続する。
規約：指定全同型の厳密等号。使われ方：Sp 正本の全核面比較への零角境界。 -/
lemma dgOdotMilnorNuNullSquareComparison_zero :
    (dgOdotMilnorNuNullSquareComparison R d h).precomp verdierZeroCorner =
      dgOdotMilnorNuNullRawSquareZeroBoundary R d h := by
  apply eq_of_heq
  exact nullSquareShortFromTriangle (dgOdotMilnorNuNullSquareComparison R d h)
    squareLeftEdge (stdSimplex.δ (0 : Fin 2)) verdierZeroCorner nullSquareZeroCorner
    rfl rfl (dgOdotMilnorNuZeroLeftDiagramComparison R d h)
    (dgOdotMilnorNuNullSquareComparison_zeroLeft R d h) _ _
    (dgOdotMilnorNuNullRawSquareZeroBoundary R d h) rfl

end SerrePositivity.KST.SConstruction
