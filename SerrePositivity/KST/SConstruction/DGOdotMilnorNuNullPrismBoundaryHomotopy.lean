module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismSideBoundary
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismTriangleFaces

/-!
概要：元比較 prism の全側境界が元実／絶対二胞体の境界を厳密に結ぶ。
方針：元三側面の始端・終端を全境界の各面で回収する。
規約：元二胞体を固定し、内部充填は主張しない。
使われ方：同じ元両二胞体を保持する全境界充填への実入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元三比較側面の始端は同じ元実二胞体の三面。
方針：同じ実ホモトピーの始端と元三面の回収を合成する。
規約：元全辺の等号。使われ方：元側境界の実二胞体への接合。 -/
lemma dgOdotMilnorNuNullPrismSideFamily_start (j : Fin 2) (i : Fin 3) :
    ι₀ ≫ dgOdotMilnorNuNullPrismSideFamily R d h j i =
      boundary.ι i ≫ (boundary 2).ι ≫
        SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j) := by
  rw [← Category.assoc, boundary.ι_ι]
  fin_cases i
  · change ι₀ ≫ (dgOdotMilnorNuNullPrismLastHomotopy R d h j).h =
      stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j)
    exact (dgOdotMilnorNuNullPrismLastHomotopy R d h j).h₀.trans
      (dgOdotMilnorNuNullPrismTriangle_last_actual R d j).symm
  · change ι₀ ≫ (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h =
      stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j)
    exact (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h₀.trans
      (dgOdotMilnorNuNullPrismTriangle_diagonal_actual R d j).symm
  · change ι₀ ≫ (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h =
      stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j)
    exact (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h₀.trans
      (dgOdotMilnorNuNullPrismTriangle_first_actual R d j).symm

/-- 概要：元三比較側面の終端は同じ元絶対二胞体の三面。
方針：同じ実ホモトピーの終端と元絶対三面の回収を合成する。
規約：元全辺の等号。使われ方：元側境界の絶対二胞体への接合。 -/
lemma dgOdotMilnorNuNullPrismSideFamily_end (j : Fin 2) (i : Fin 3) :
    ι₁ ≫ dgOdotMilnorNuNullPrismSideFamily R d h j i =
      boundary.ι i ≫ (boundary 2).ι ≫
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j) := by
  rw [← Category.assoc, boundary.ι_ι]
  fin_cases i
  · change ι₁ ≫ (dgOdotMilnorNuNullPrismLastHomotopy R d h j).h =
      stdSimplex.δ (0 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j)
    exact (dgOdotMilnorNuNullPrismLastHomotopy R d h j).h₁.trans
      (dgOdotMilnorNuNullPrismTriangle_last_absolute R d h j).symm
  · change ι₁ ≫ (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h =
      stdSimplex.δ (1 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j)
    exact (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h₁.trans
      (dgOdotMilnorNuNullPrismTriangle_diagonal_absolute R d h j).symm
  · change ι₁ ≫ (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h =
      stdSimplex.δ (2 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j)
    exact (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h₁.trans
      (dgOdotMilnorNuNullPrismTriangle_first_absolute R d h j).symm

/-- 概要：元全側境界の始端は元実二胞体の境界全体。
方針：元全境界の各面で同じ元始端を回収する。
規約：全単体の厳密等号。使われ方：全境界充填の元実二胞体。 -/
lemma dgOdotMilnorNuNullPrismSideBoundary_start (j : Fin 2) :
    ι₀ ≫ dgOdotMilnorNuNullPrismSideBoundary R d h j =
      (boundary 2).ι ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j) := by
  apply boundary.hom_ext
  intro i
  rw [← ι₀_comp_assoc, dgOdotMilnorNuNullPrismSideBoundary_faces]
  exact dgOdotMilnorNuNullPrismSideFamily_start R d h j i

/-- 概要：元全側境界の終端は元絶対二胞体の境界全体。
方針：元全境界の各面で同じ元終端を回収する。
規約：全単体の厳密等号。使われ方：全境界充填の元絶対二胞体。 -/
lemma dgOdotMilnorNuNullPrismSideBoundary_end (j : Fin 2) :
    ι₁ ≫ dgOdotMilnorNuNullPrismSideBoundary R d h j =
      (boundary 2).ι ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j) := by
  apply boundary.hom_ext
  intro i
  rw [← ι₁_comp_assoc, dgOdotMilnorNuNullPrismSideBoundary_faces]
  exact dgOdotMilnorNuNullPrismSideFamily_end R d h j i

/-- 概要：元実／絶対二胞体の元境界を結ぶ同じ指定三側面付き実ホモトピー。
方針：同じ全側境界と同じ元二端点等号を構造へ束ねる。
規約：内部二胞体への延長は別工程。使われ方：元全境界充填の実入力。 -/
def dgOdotMilnorNuNullPrismBoundaryHomotopy (j : Fin 2) : SSet.Homotopy
    ((boundary 2).ι ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j))
    ((boundary 2).ι ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j)) where
  h := dgOdotMilnorNuNullPrismSideBoundary R d h j
  h₀ := dgOdotMilnorNuNullPrismSideBoundary_start R d h j
  h₁ := dgOdotMilnorNuNullPrismSideBoundary_end R d h j
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

end SerrePositivity.KST.SConstruction
