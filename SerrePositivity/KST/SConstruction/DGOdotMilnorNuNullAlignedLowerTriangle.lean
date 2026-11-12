module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullAlignedDiagonal
public import SerrePositivity.KST.SConstruction.SpecifiedTriangleDiagonalRepresentative
/-!
概要：元下全三角形比較の類を保ち、元上比較との共有対角を厳密に合わせる。
方針：対角制限の inner fibration と同じ類の辺の代表修正を使う。
規約：元実／絶対両二胞体と元比較の全関手同型の類を保持する。
使われ方：元二三角形を貼る核零化面の全比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
private lemma nullTriangleEdgeYoneda {A X : SSet.{u}} (p : A ⟶ X)
    (s : A _⦋1⦌) (t : X _⦋1⦌) (h : p.app (Opposite.op ⦋1⦌) s = t) :
    SSet.yonedaEquiv.symm s ≫ p = SSet.yonedaEquiv.symm t := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h
private lemma nullTriangleRepresentative {X : SSet.{u}} [Quasicategory X]
    {f g : (Δ[2] : SSet.{u}) ⟶ X} (H₀ : SSet.Homotopy f g)
    (T : SSet.Homotopy (stdSimplex.δ (1 : Fin 3) ≫ f)
      (stdSimplex.δ (1 : Fin 3) ≫ g))
    (hc₀ : SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀).map
          ((truncation 2).map ((pre (stdSimplex.δ (1 : Fin 3))).app X))) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy T)) :
    ∃ H : SSet.Homotopy f g,
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ H.h = T.h ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀) := by
  exact exists_specifiedTriangleDiagonalRepresentative H₀ T hc₀
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
/-- 概要：元下比較の類を保つ同じ両二胞体の比較は、元上比較と全対角を共有できる。
方針：元の対角制限の辺を、同じ類を持つ元上対角辺へ厳密に修正する。
規約：全射の等号と元全比較の類を同時に保持する。
使われ方：元の二三角形の実比較を正方形へ貼る。 -/
lemma dgOdotMilnorNuNullAlignedLowerTriangle_exists :
    ∃ H : SSet.Homotopy
        (SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d 1))
        (SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h 1)),
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 2})) ≫ H.h =
          (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h ∧
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
          SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
            (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)) := by
  exact nullTriangleRepresentative (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)
    (dgOdotMilnorNuNullLowerAlignedDiagonalHomotopy R d h)
    (dgOdotMilnorNuNullLowerAlignedDiagonalHomotopy_class R d h)
/-- 概要：元上比較と同じ対角を持つ元下全三角形比較の実ホモトピー。
方針：同じ両二胞体・同じ全比較の類を保つ代表を選ぶ。
規約：新しい二胞体は選ばない。使われ方：元核面の全ホモトピーの貼り合わせ。 -/
def dgOdotMilnorNuNullAlignedLowerTriangleHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d 1))
    (SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h 1)) :=
  Classical.choose (dgOdotMilnorNuNullAlignedLowerTriangle_exists R d h)
/-- 概要：同じ元下全比較の対角は元上比較の対角と全単体で一致する。
方針：元代表修正の第一の回収式。
規約：厳密な全射の等号。使われ方：元二三角形の比較の貼り合わせ。 -/
lemma dgOdotMilnorNuNullAlignedLowerTriangleHomotopy_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h).h =
      (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h :=
  (Classical.choose_spec (dgOdotMilnorNuNullAlignedLowerTriangle_exists R d h)).1
/-- 概要：同じ元下全比較の元関手圏の射の類は元比較そのもの。
方針：元代表修正の第二の回収式。
規約：全三角形の同型を保持。使われ方：指定短辺比較の厳密回収。 -/
lemma dgOdotMilnorNuNullAlignedLowerTriangleHomotopy_class :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)) :=
  (Classical.choose_spec (dgOdotMilnorNuNullAlignedLowerTriangle_exists R d h)).2
end SerrePositivity.KST.SConstruction
