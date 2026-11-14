module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCellNuComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCompletedLandTamme
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRelativeSourceRoof

/-!
概要：元 native 対角始域と同じ固定 S 入力の ν 値を指定同値で回収する。
方針：同じ Yoneda 比較を完備な元始域に適用し、実 cell 増大との全自然性を保つ。
規約：native Verdier 列と LT 極限錐の元始域はそのまま保つ。
使われ方：同じ増大屋根の回収と、元 LT 錐頂点から固定 ν 始域値への比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants Spectra

open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d))
local notation "T" => DGCategoryCellResolution.Source R (A)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (A) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSource_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (T) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (A)

/-- 概要：元 native 対角始域から同じ固定 ν 値への指定同値。
方針：同じ実 Yoneda と元小 Perf の coherent 完備性を使用する。
規約：元始域の型を変更しない。使われ方：同じ増大屋根の終端比較。 -/
def dgOdotMilnorSourceNativeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d).obj
    (dgKInputStableValue R (dgOdotDiagonalSourceInput R d)).obj :=
  (dgKNativeValueComparison_isQCatEquivalence R (A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d)).choose

/-- 概要：同じ元 native 始域比較を完全射として保持する。
方針：指定同値の完全性を使用する。規約：同じ順方向を保つ。
使われ方：Cat^perf 内の元始域回収。 -/
def dgOdotMilnorSourceNativeComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d)
    (dgKInputStableValue R (dgOdotDiagonalSourceInput R d)) :=
  ⟨(dgOdotMilnorSourceNativeValueEquivalence R d).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorSourceNativeValueEquivalence R d).isQCatEquivalence⟩

/-- 概要：同じ元 native 始域と固定 ν 始域は Cat^perf の実頂点として同型。
方針：同じ完全同値の Cat^perf 辺の可逆性を使用する。
規約：別の完備化模型で置換しない。使われ方：同じ不変量の始域値の回収。 -/
def dgOdotMilnorSourceNativePerfectIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (perfectStableVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d))
    (perfectStableVertex (dgKInputStableValue R (dgOdotDiagonalSourceInput R d))
      (dgKInputStableValue_isIdempotentComplete R _)) := by
  let f := dgOdotMilnorSourceNativeComparison R d
  let hA := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d
  let hB := dgKInputStableValue_isIdempotentComplete R (dgOdotDiagonalSourceInput R d)
  letI : IsIso (perfectStableHoArrow f hA hB) :=
    perfectStableHoArrow_isIso_of_isQCatEquivalence f hA hB
      (dgOdotMilnorSourceNativeValueEquivalence R d).isQCatEquivalence
  exact asIso (perfectStableHoArrow f hA hB)

/-- 概要：元 native 始域の不変量値と同じ固定 S 始域値の指定同型。
方針：同じ Cat^perf 頂点同型を元の実関手で写す。
規約：不変量の局所化条件は不要。使われ方：LT 錐の元頂点と相対値の照合。 -/
def dgOdotMilnorSourceNativeValueIso (E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (E.app _ (perfectStableVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d)))
      ((dgKInputPerfectNu R ≫ E).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d))) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso _ (E.app _ ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d))))
  rw [dgKInputPerfectNu_vertex]
  exact (dgOdotMilnorSourceNativePerfectIso R d).map E

/-- 概要：元 LT 極限錐の同じ頂点から固定 S 始域の不変量値への指定同型。
方針：元頂点の厳密回収式と同じ native 比較を使用する。
規約：極限錐自体の頂点を変更しない。使われ方：e② の元始域の回収。 -/
def dgOdotMilnorCompletedLandTammeCone_sourceValueIso (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
    {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}} (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgOdotMilnorCompletedLandTammeCone R d h hE).vertex
      ((dgKInputPerfectNu R ≫ E).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d))) := by
  rw [dgOdotMilnorCompletedLandTammeCone_source]
  exact dgOdotMilnorSourceNativeValueIso R d E

/-- 概要：同じ元始域の実 cell 増大は native／固定 ν の比較と全自然に可換。
方針：元の厳密増大に同じ Yoneda・評価自然性を適用する。
規約：増大屋根の二辺と元終端を保つ。使われ方：始域回収の指定二胞体。 -/
def dgOdotMilnorSourceAugmentationNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorSourceCellNativeValueEquivalence R d).hom ≫
      (dgOdotMilnorSourceAugmentationExactMap R d).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (A)) ≫
      (dgOdotMilnorSourceNativeValueEquivalence R d).hom) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKNativeValueComparison R (T) ≫
    (dgKNativeInputExactMap R (T) (A) (DGCategoryCellResolution.augmentation R (A))).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (A)) ≫ dgKNativeValueComparison R (A))
  exact dgKNativeNuNaturality R (T) (A) (DGCategoryCellResolution.augmentation R (A))

end SerrePositivity.KST.SConstruction
