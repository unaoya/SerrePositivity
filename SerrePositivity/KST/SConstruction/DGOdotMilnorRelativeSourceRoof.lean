module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceSquare
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof

/-!
概要：元対角始域への実増大屋根を Sp の完備化付き始域回収へ接続する。
方針：同じ二本の S 辺の Cat^perf 像から指定同型と可換三角形を構成する。
規約：始域の頂点等号や S 内の逆射を追加入力にしない。
使われ方：d④ の採用済み屋根版と全 Cat^perf 不変量の元始域値の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ実増大・厳密核比較を持つ、元始域への完備化付き相対屋根。
方針：同じ二辺の可逆な ν 像から指定同型と三角形を取る。
規約：各辺の可逆性は Milnor 条件と実準同値から証明する。
使われ方：Sp の相対長方形の元始域回収。 -/
def dgOdotMilnorRelativeSourceRoof : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof
    (dgKInputPerfectNu.{u, u + 1} R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d)) := by
  let a := (hoFunctor.map (dgKInputPerfectNu R)).toFunctor.map
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceAugmentationInputMap R d)).toTruncated)
  let b := (hoFunctor.map (dgKInputPerfectNu R)).toFunctor.map
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceKernelInputMap R d)).toTruncated)
  letI ha : IsIso a := dgKInputPerfectNu_map_isIso_of_isQCatEquivalence R
    (dgOdotMilnorSourceAugmentationInputMap R d)
    (dgOdotMilnorSourceAugmentationNu_isQCatEquivalence R d)
  letI hb : IsIso b := dgKInputPerfectNu_map_isIso_of_isQCatEquivalence R
    (dgOdotMilnorSourceKernelInputMap R d)
    (dgOdotMilnorSourceKernelNu_isQCatEquivalence R d h)
  let image := (@asIso _ _ _ _ a ha).symm ≪≫ (@asIso _ _ _ _ b hb)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorSourceCellInput R d),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceAugmentationInputMap R d)).toTruncated,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceKernelInputMap R d)).toTruncated,
    ha, hb, image, ?_⟩
  change a ≫ (inv a ≫ b) = b
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- 概要：同じ実屋根は全 Cat^perf 不変量で元始域値を核値へ指定同型で戻す。
方針：Sp 正本の同じ屋根値を使用する。規約：元入力の実頂点を保持する。
使われ方：実 LT 長方形の始域値との接続。 -/
def dgOdotMilnorRelativeSourceValueIso
    (E : perfectStableInfinity.{u + 1} ⟶ Spectra.Sp.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((dgKInputPerfectNu R ≫ E).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)))
      ((dgKInputPerfectNu R ≫ E).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d))) :=
  (dgOdotMilnorRelativeSourceRoof R d h).valueIso E

end SerrePositivity.KST.SConstruction
