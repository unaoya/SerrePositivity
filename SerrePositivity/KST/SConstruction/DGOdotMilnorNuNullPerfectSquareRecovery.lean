module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullRawSquareDiagramIso
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulNormalizedIsoRecovery
/-!
概要：元全核四角形の Cat^perf 比較は、包含後に元実 ν 全比較とその全制限を回収する。
方針：同じ充満忠実な完備包含の正規化付き逆像の厳密回収を使う。
規約：元の全比較を選び直さない。
使われ方：Cat^perf の既存指定三境界との照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
/-- 概要：元全核面の Cat^perf 比較は包含後に元 ν 全比較そのものを回収する。
方針：同じ完備包含の逆像の全関手同型の回収を使う。
規約：元の二四角形と全同型。使われ方：元指定三境界の比較の反映。 -/
lemma dgOdotMilnorNuNullPerfectSquareComparison_postcomp_heq :
    HEq ((dgOdotMilnorNuNullPerfectSquareComparison R d h).postcomp
      perfectStableInfinityInclusion) (dgOdotMilnorNuNullSquareComparison R d h) := by
  have ha : dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) ≫
        perfectStableInfinityInclusion := by
    rw [Category.assoc, dgKInputPerfectNu_inclusion]
  have hb : perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) =
      (dgOdotMilnorNuPerfectSequence R d h).presentation.square ≫
        perfectStableInfinityInclusion :=
    (perfectVerdierSquare_inclusion (dgOdotMilnorNuPerfectSequence R d h)).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsFullyFaithful.preimageNormalizedFunctorIso_postcomp_heq
    perfectStableInfinityInclusion_isFullyFaithful
      (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
      (dgOdotMilnorNuPerfectSequence R d h).presentation.square
      (dgOdotMilnorNuNullSquareComparison R d h) ha hb
/-- 概要：元全核面 Cat^perf 比較の任意の制限は包含後にも同じ元 ν 比較の制限。
方針：元全比較の回収と前後合成の交換を同じ全制限へ適用する。
規約：全単体・全射を保持。使われ方：包含・商・零角の指定境界の照合。 -/
lemma dgOdotMilnorNuNullPerfectSquareComparison_precomp_postcomp_heq
    {A : SSet.{u + 2}} (q : A ⟶ Δ[1] ⊗ Δ[1]) :
    HEq (((dgOdotMilnorNuNullPerfectSquareComparison R d h).precomp q).postcomp
      perfectStableInfinityInclusion) ((dgOdotMilnorNuNullSquareComparison R d h).precomp q) := by
  have ha : dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) ≫
        perfectStableInfinityInclusion := by
    rw [Category.assoc, dgKInputPerfectNu_inclusion]
  have hb : perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) =
      (dgOdotMilnorNuPerfectSequence R d h).presentation.square ≫
        perfectStableInfinityInclusion :=
    (perfectVerdierSquare_inclusion (dgOdotMilnorNuPerfectSequence R d h)).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsFullyFaithful.preimageNormalizedFunctorIso_precomp_postcomp_heq
    perfectStableInfinityInclusion_isFullyFaithful
      (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
      (dgOdotMilnorNuPerfectSequence R d h).presentation.square
      (dgOdotMilnorNuNullSquareComparison R d h) ha hb q
end SerrePositivity.KST.SConstruction
