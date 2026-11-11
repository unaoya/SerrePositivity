module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorKernelOuterSquareDiagramIso
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullLowerTriangleComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPerfectSquareDiagramIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：LT 外周の同じ下二単体を厚核面へ運び、公開済みの厚核下二単体比較へ接続する。
方針：7404a60a5 の全外周認証を三角形へ制限し、同じ実／絶対比較と合成する。
規約：共通 S 長方形の下合成二単体の実構成とは区別する。
使われ方：K-S2 の厚核側下指定二単体の供給部品。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：LT 外周の元下二単体から元厚核面の指定下二単体への全比較。
方針：外周全認証の同じ制限を使う。規約：二単体を選び直さない。
使われ方：厚核側下二単体の移送。 -/
def dgOdotTailKernelLowerTriangleComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (dgOdotMilnorActualOuterDiagram R d h).square)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) :=
  (dgOdotMilnorKernelOuterSquareDiagramIso R d h).comparison.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1)

/-- 概要：厚核面全比較の同じ下制限を Cat^perf の指定値として取る。
方針：公開全比較を制限する。規約：包含後の元指定値は次の補題で回収。
使われ方：全外周比較と下二単体比較を同時に保持する。 -/
def dgOdotTailKernelSpecifiedLowerComparison :=
  (dgOdotMilnorNuNullPerfectSquareComparison R d h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1)

/-- 概要：同じ下制限は包含後に元の指定下二単体比較そのものを回収する。
方針：Cat^perf 回収と元全核面の指定下制限を合成する。
規約：存在だけでなく指定同型を保持。使われ方：厚核下二単体の認証。 -/
lemma dgOdotTailKernelSpecifiedLowerComparison_recovery :
    HEq ((dgOdotTailKernelSpecifiedLowerComparison R d h).postcomp
      perfectStableInfinityInclusion) (dgOdotMilnorNuNullLowerTriangleComparison R d h) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq
    ((dgOdotMilnorNuNullSquareComparison R d h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1))
    (Equiv.symm_apply_apply SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)).symm
    (Equiv.symm_apply_apply SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))).symm
  have hr := ht.symm.trans (heq_of_eq (dgOdotMilnorNuNullSquareComparison_lower R d h))
  exact (dgOdotMilnorNuNullPerfectSquareComparison_precomp_postcomp_heq R d h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1)).trans hr

/-- 概要：LT 外周の下二単体を同じ厚核列の絶対下二単体へ接続する。
方針：移送後に公開済みの実／絶対下二単体全比較を合成する。
規約：元の厚核包含・cell 射影・実完備化を保持。使われ方：指定下二単体の絶対側接続。 -/
def dgOdotTailKernelAbsoluteLowerTriangleComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (dgOdotMilnorActualOuterDiagram R d h).square)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square) :=
  dgOdotTailKernelLowerTriangleComparison R d h ≪≫
    dgOdotTailKernelSpecifiedLowerComparison R d h

/-- 概要：LT 外周から絶対厚核面への全比較の下制限は同じ指定合成比較。
方針：全比較の前合成の合成則を使う。規約：下二単体を後から選ばない。
使われ方：共通長方形に渡す厚核側の全図式整合。 -/
lemma dgOdotTailKernelAbsoluteLowerTriangle_whole :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp ((dgOdotMilnorKernelOuterSquareDiagramIso R d h).comparison ≪≫
      dgOdotMilnorNuNullPerfectSquareComparison R d h) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) =
      dgOdotTailKernelAbsoluteLowerTriangleComparison R d h := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans _ _ _

/-- 概要：共通長方形の外面下二単体を厚核面の指定下二単体へ接続する。
方針：実外面認証の逆と既存 LT→厚核比較を下三角形で合成する。
規約：全長方形認証を要求せず、外面だけを明示入力にする。
使われ方：③ の長方形構成中にも循環せず使える厚核下二単体接続。 -/
def dgOdotTailActualKernelLowerTriangleComparison
    {F : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ perfectStableInfinity.{u + 1}}
    {b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (dgOdotMilnorActualOuterDiagram R d h).square F}
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (dgOdotMilnorActualOuterDiagram R d h).square F b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.comparison.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) ≪≫
    dgOdotTailKernelLowerTriangleComparison R d h

/-- 概要：共通実外面の下二単体から、同じ指定値を持つ絶対厚核下二単体への接続。
方針：厚核の指定下比較を同じ実外面比較に後続させる。
規約：指定元二単体・元完備化先を保持。使われ方：実構成到着時の厚核側代入。 -/
def dgOdotTailActualKernelAbsoluteLowerTriangleComparison
    {F : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ perfectStableInfinity.{u + 1}}
    {b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (dgOdotMilnorActualOuterDiagram R d h).square F}
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (dgOdotMilnorActualOuterDiagram R d h).square F b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square) :=
  dgOdotTailActualKernelLowerTriangleComparison R d h e ≪≫
    dgOdotTailKernelSpecifiedLowerComparison R d h

/-- 概要：下二単体比較の包含短辺は元外周認証の指定包含比較。
方針：同じ三角形の二番面と元全認証の制限を照合する。
規約：同型の等号を保つ。使われ方：指定包含境界の回収。 -/
lemma dgOdotTailKernelLowerTriangle_inclusion :
    HEq ((dgOdotTailKernelLowerTriangleComparison R d h).precomp
      (stdSimplex.δ (2 : Fin 3)))
      (dgOdotMilnorKernelOuterSquareBoundary R d h).inclusion := by
  unfold dgOdotTailKernelLowerTriangleComparison
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp]
  change HEq ((dgOdotMilnorKernelOuterSquareDiagramIso R d h).comparison.precomp
    (stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1)) _
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge]
  exact heq_of_eq (dgOdotMilnorKernelOuterSquareDiagramIso R d h).inclusion_eq

/-- 概要：下二単体比較の商短辺も元外周認証の指定商比較。
方針：同じ三角形の零番面を使う。規約：商辺だけで全比較を代用しない。
使われ方：指定商境界の回収。 -/
lemma dgOdotTailKernelLowerTriangle_quotient :
    HEq ((dgOdotTailKernelLowerTriangleComparison R d h).precomp
      (stdSimplex.δ (0 : Fin 3)))
      (dgOdotMilnorKernelOuterSquareBoundary R d h).quotient := by
  unfold dgOdotTailKernelLowerTriangleComparison
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp]
  change HEq ((dgOdotMilnorKernelOuterSquareDiagramIso R d h).comparison.precomp
    (stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge]
  exact heq_of_eq (dgOdotMilnorKernelOuterSquareDiagramIso R d h).quotient_eq
end SerrePositivity.KST.SConstruction
