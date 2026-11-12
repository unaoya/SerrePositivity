module
public import SerrePositivity.KST.SConstruction.KSuspensionMappingTriangles
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition
public import SerrePositivity.KST.Spectra.PointedMappingHomotopy
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 元の K の prism から復号した実際の適合ホモトピー
概要：元の各段の自然性 square の二つの三角形から、構造可換式の実ホモトピーを作る。
方針：二つの復号した辺を元の三角形と逆・合成の証人を保持して Kan 写像空間で合成する。
規約：元の全点つき対象の nerve を Kan と仮定せず、標的が Kan な写像空間でのみ合成する。
使われ方：元の prism とパラメータ付き相対厳密化の入力との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kSuspensionCompatibility_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の二つの三角形の復号と、両逆三角形・合成三角形を保持する適合辺の選択。 -/
def kKanSuspensionCompatibilityComposition {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition
      (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F f))
      (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f)) := by
  letI : KanComplex (SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space)
      ((kKanSequence (F.obj j)).level (r + 1)).space) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.kanMappingSpanComposition _ _

/-- 元の square の復号から作る、固定構造射との適合条件の実際の写像空間の辺。 -/
def kKanSuspensionCompatibilityEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space)
      ((kKanSequence (F.obj j)).level (r + 1)).space).right.Edge
      (familyVertex ((kKanSequence (F.obj i)).sigma r ≫ kKanSequenceLevelMap (F.map f) (r + 1)))
      (familyVertex (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r ≫
        (kKanSequence (F.obj j)).sigma r)) :=
  (kKanSuspensionCompatibilityComposition r F f).edge.ofEq
    (familyVertex_eq_pointedHomVertex _).symm (familyVertex_eq_pointedHomVertex _).symm

/-- 全段で、元の構造射と元の段の射の二つの合成を結ぶ実際の基点固定ホモトピー。 -/
def kKanSuspensionCompatibilityHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    SSet.Homotopy
      (((kKanSequence (F.obj i)).sigma r ≫ kKanSequenceLevelMap (F.map f) (r + 1)).right)
      ((PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r ≫
        (kKanSequence (F.obj j)).sigma r).right) :=
  homotopyOfEdge (kKanSuspensionCompatibilityEdge r F f)

/-- 復号した実適合ホモトピーは全時刻で元の基点を固定する。 -/
lemma kKanSuspensionCompatibilityHomotopy_base {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space).hom ▷ (Δ[1] : SSet.{u}) ≫
      (kKanSuspensionCompatibilityHomotopy r F f).h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((kKanSequence (F.obj j)).level (r + 1)).space.hom :=
  homotopyOfEdge_base (kKanSuspensionCompatibilityEdge r F f)

end SerrePositivity.KST.SConstruction
