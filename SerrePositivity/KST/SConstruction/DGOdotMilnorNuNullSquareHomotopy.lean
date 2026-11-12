module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullAlignedLowerTriangle
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutHomotopy
/-!
概要：元実／絶対零化四角形全体の比較を、元の両二胞体を保って貼り合わせる。
方針：元上比較と同じ対角を持つ元下比較を、正方形の三角形分解で貼る。
規約：元の全四角形を保持し、元下比較の全関手同型の類も保持する。
使われ方：指定三境界付き実 ν 核面の全比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
/-- 概要：元四角形の上三角形の比較を元の実二胞体の表示で保持する。
方針：同じ元上ホモトピーの二端点を Yoneda の往復で回収する。
規約：全射は元上比較そのもの。使われ方：正方形全体への貼り合わせ。 -/
def dgOdotMilnorNuNullSquareUpperHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) where
  h := (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h
  h₀ := (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h₀.trans
    (Equiv.symm_apply_apply SSet.yonedaEquiv _)
  h₁ := (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h₁.trans
    (Equiv.symm_apply_apply SSet.yonedaEquiv _)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
/-- 概要：元四角形の下三角形に、共有対角を厳密に合わせた元全比較を置く。
方針：元比較の類を保つ代表の端点だけを Yoneda の往復で回収する。
規約：元両二胞体を保持。使われ方：元上三角形との厳密な貼り合わせ。 -/
def dgOdotMilnorNuNullSquareLowerHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) where
  h := (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h).h
  h₀ := (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h).h₀.trans
    (Equiv.symm_apply_apply SSet.yonedaEquiv _)
  h₁ := (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h).h₁.trans
    (Equiv.symm_apply_apply SSet.yonedaEquiv _)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
/-- 概要：元上下二胞体の実全比較は同じ共有対角上で厳密に一致する。
方針：同じ元上対角へ回収する代表修正の全射等号。
規約：全時刻・全単体の等号。使われ方：元全四角形比較の構成。 -/
lemma dgOdotMilnorNuNullSquareHomotopy_gluing :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullSquareUpperHomotopy R d h).h =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullSquareLowerHomotopy R d h).h :=
  (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy_diagonal R d h).symm
/-- 概要：元実 ν 零化四角形と元絶対零化四角形の実全比較ホモトピー。
方針：元上二胞体と元下二胞体の比較を同じ厳密対角に沿って貼る。
規約：元両二胞体の全単体を保持。使われ方：実 ν 核面の全図式比較。 -/
def dgOdotMilnorNuNullSquareHomotopy : SSet.Homotopy
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout (dgOdotMilnorNuNullSquareUpperHomotopy R d h)
    (dgOdotMilnorNuNullSquareLowerHomotopy R d h) (dgOdotMilnorNuNullSquareHomotopy_gluing R d h)
/-- 概要：元全四角形比較の上三角形制限は元上全比較そのもの。
方針：同じ pushout の左包含の計算。
規約：元の全射の厳密等号。使われ方：指定上二胞体と短辺比較の回収。 -/
lemma dgOdotMilnorNuNullSquareHomotopy_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullSquareHomotopy R d h).h =
      (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inl _ _ _ _
/-- 概要：元全四角形比較の下三角形制限は元比較の類を保つ同じ実代表。
方針：同じ pushout の右包含の計算。
規約：元の全射の厳密等号。使われ方：指定下二胞体と短辺比較の類の回収。 -/
lemma dgOdotMilnorNuNullSquareHomotopy_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullSquareHomotopy R d h).h =
      (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inr _ _ _ _
end SerrePositivity.KST.SConstruction
