module
public import SerrePositivity.KST.SConstruction.KSuspensionCompatibilityHomotopy
public import SerrePositivity.KST.SConstruction.MonicKSequenceMaps
public import SerrePositivity.KST.SConstruction.SequenceCompatibilityTransport

/-! # 元の prism の適合辺を単射置換した源へ移す
概要：元の全段の実適合辺を、元の射影で前合成して厳密化の既存の段の射へ合わせる。
方針：写像空間の源の制限と、元の列の射影の厳密な構造可換式を使う。
規約：元の適合辺と元の単射置換の射影を固定する。
使われ方：元の prism から、BF 列の厳密化に用いる指定した実ホモトピーへの接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 元の prism の辺を元の射影で前合成した、単射な源からの指定適合辺。 -/
def monicKPrismCompatibilityEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((monicKKanSequence (F.obj i)).level r).space)
      ((kKanSequence (F.obj j)).level (r + 1)).space).right.Edge
      (familyVertex ((monicKKanSequence (F.obj i)).sigma r ≫
        monicKToRawLevelMap (F.map f) (r + 1)))
      (familyVertex (PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap (F.map f) r ≫
        (kKanSequence (F.obj j)).sigma r)) :=
  sequenceCompatibilityEdge_precompose (monicKKanSequenceProjection (F.obj i))
    (kKanSequenceLevelMap (F.map f)) r (kKanSuspensionCompatibilityEdge r F f)

/-- 厳密化に用いる元の段の射について、prism から得た実適合ホモトピー。 -/
def monicKPrismCompatibilityHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) : SSet.Homotopy
      (((monicKKanSequence (F.obj i)).sigma r ≫
        monicKToRawLevelMap (F.map f) (r + 1)).right)
      ((PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap (F.map f) r ≫
        (kKanSequence (F.obj j)).sigma r).right) :=
  homotopyOfEdge (monicKPrismCompatibilityEdge r F f)

/-- 源を元の単射置換へ移しても、全時刻で元の基点を固定する。 -/
lemma monicKPrismCompatibilityHomotopy_base {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((monicKKanSequence (F.obj i)).level r).space).hom ▷ (Δ[1] : SSet.{u}) ≫
      (monicKPrismCompatibilityHomotopy r F f).h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((kKanSequence (F.obj j)).level (r + 1)).space.hom :=
  homotopyOfEdge_base (monicKPrismCompatibilityEdge r F f)

end SerrePositivity.KST.SConstruction
