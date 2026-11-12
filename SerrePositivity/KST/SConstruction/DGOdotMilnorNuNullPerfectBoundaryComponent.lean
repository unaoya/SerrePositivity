module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPerfectSquareRecovery
/-!
概要：元実 ν 核面の指定全境界比較を、同じ Cat^perf 境界の指定比較へ戻す。
方針：元 ν の全単体の回収で端点を合わせ、充満忠実な完備包含の同じ逆像を取る。
規約：元の指定同型を包含後に厳密回収する。
使われ方：Sp 正本の Cat^perf 指定三境界付き核面比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
/-- 概要：元核面の同じ指定全比較を同じ Cat^perf の境界比較へ戻す。
方針：元全境界の厳密回収で端点だけを正規化し、充満忠実な包含の逆像を取る。
規約：指定全同型の値を保持。使われ方：元三境界を保つ全比較。 -/
def dgOdotMilnorNuNullPerfectBoundaryComponent {A : SSet.{u + 2}}
    (q : A ⟶ Δ[1] ⊗ Δ[1])
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
      (q ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
      (q ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square) :=
  perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e
      (by rw [Category.assoc, Category.assoc, dgKInputPerfectNu_inclusion])
      (by
        exact (congrArg (fun f => q ≫ f)
          (perfectVerdierSquare_inclusion (dgOdotMilnorNuPerfectSequence R d h)).symm).trans
            (Category.assoc _ _ _).symm))
/-- 概要：同じ Cat^perf の元境界比較は包含後に元指定全比較を回収する。
方針：同じ正規化付き逆像の全関手同型の回収を使う。
規約：元全比較そのもの。使われ方：三境界の指定値の保持。 -/
lemma dgOdotMilnorNuNullPerfectBoundaryComponent_postcomp_heq {A : SSet.{u + 2}}
    (q : A ⟶ Δ[1] ⊗ Δ[1])
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
      (q ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))) :
    HEq ((dgOdotMilnorNuNullPerfectBoundaryComponent R d h q e).postcomp
      perfectStableInfinityInclusion) e := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsFullyFaithful.preimageNormalizedFunctorIso_postcomp_heq
    perfectStableInfinityInclusion_isFullyFaithful _ _ e _ _
/-- 概要：元全核面 Cat^perf 比較の制限は、元指定境界比較の同じ逆像そのもの。
方針：包含後に同じ元指定比較を回収し、充満忠実性で同型の等号を戻す。
規約：境界比較を選び直さない。使われ方：Sp 正本の全図式比較の境界則。 -/
lemma dgOdotMilnorNuNullPerfectBoundaryComponent_eq_precomp {A : SSet.{u + 2}}
    (q : A ⟶ Δ[1] ⊗ Δ[1])
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
      (q ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)))
    (he : (dgOdotMilnorNuNullSquareComparison R d h).precomp q = e) :
    (dgOdotMilnorNuNullPerfectSquareComparison R d h).precomp q =
      dgOdotMilnorNuNullPerfectBoundaryComponent R d h q e := by
  apply perfectStableInfinityInclusion_isFullyFaithful.postcomp_functorIso_injective
  apply eq_of_heq
  exact (dgOdotMilnorNuNullPerfectSquareComparison_precomp_postcomp_heq R d h q).trans
    ((heq_of_eq he).trans
      (dgOdotMilnorNuNullPerfectBoundaryComponent_postcomp_heq R d h q e).symm)
end SerrePositivity.KST.SConstruction
