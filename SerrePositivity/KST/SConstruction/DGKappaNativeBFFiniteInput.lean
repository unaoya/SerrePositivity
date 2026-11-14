module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFPointedStages
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentFullSubcategoryRestriction

/-!
概要：同じ未完備 native 一四角形の頂点だけを持つ豊穣入力を固定する。
方針：元の四角形の頂点像の充満部分圏へ、同じ全二胞体を制限する。
規約：全 Hom を保つ。一般の安定圏上の BF 関手化を行わない。
使われ方：有限 BF 再帰構成の入力と、元の実四角形への厳密な回収。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open LocalizingInvariants NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ元の四角形の頂点に現れる安定値の条件。
方針：元の頂点像をそのまま条件にする。
規約：完備化を含まない。使われ方：一四角形への入力制限。 -/
def dgKappaNativeBFVertexProperty : ObjectProperty _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v} :=
  fun C => ∃ x, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject
    ((dgKappaNativeVerdierDiagram.{u, v} R D I).square.app (Opposite.op ⦋0⦌) x) = C

/-- 概要：同じ四頂点像と元の全 Hom だけを保持する入力圏。
方針：同じ頂点条件の充満部分圏を取る。
規約：射を離散化しない。使われ方：有限 BF 構成の定義域。 -/
abbrev DGKappaNativeBFFiniteInput := (dgKappaNativeBFVertexProperty.{u, v} R D I).FullSubcategory

/-- 概要：元の全 Hom を保つ有限入力の豊穣包含。
方針：既存の充満部分圏包含を使う。
規約：元の安定値へ厳密に戻る。使われ方：正段の全作用の制限。 -/
def dgKappaNativeBFFiniteInclusion :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion (dgKappaNativeBFVertexProperty.{u, v} R D I)

/-- 概要：同じ元の二胞体を有限入力の coherent nerve に保持する。
方針：元の頂点像の証人で元の全四角形を制限する。
規約：別の充填を選ばない。使われ方：新 BF 四辺の同時構成の元入力。 -/
def dgKappaNativeBFFiniteSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
      SimplicialNerve (DGKappaNativeBFFiniteInput.{u, v} R D I) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryLift (dgKappaNativeBFVertexProperty.{u, v} R D I)
    (dgKappaNativeVerdierDiagram.{u, v} R D I).square (fun x => ⟨x, rfl⟩)

/-- 概要：同じ有限入力四角形は元の未完備全四角形へ厳密に戻る。
方針：充満部分圏制限の全次数の包含式を使う。
規約：元の二胞体を保持する。使われ方：K-B の元の正段図式との比較。 -/
lemma dgKappaNativeBFFiniteSquare_inclusion :
    dgKappaNativeBFFiniteSquare.{u, v} R D I ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKappaNativeBFFiniteInclusion.{u, v} R D I) =
      (dgKappaNativeVerdierDiagram.{u, v} R D I).square :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryLift_inclusion
    (dgKappaNativeBFVertexProperty.{u, v} R D I)
    (dgKappaNativeVerdierDiagram.{u, v} R D I).square (fun x => ⟨x, rfl⟩)

end SerrePositivity.KST.SConstruction
