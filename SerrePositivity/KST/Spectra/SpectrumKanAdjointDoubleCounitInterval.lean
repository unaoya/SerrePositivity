module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCounitEndpoint

/-!
概要：元の構造区間を、通常と符号付きの二重随伴を結ぶ同じ実区間として保持する。
方針：証明済みの両端の座標式で表示だけを変え、元の辺と全区間の射を保存する。
規約：区間の選択を変更しない。収縮や二端点の一致は未主張。
使われ方：HA §1.4.2。円交換・符号反転の残差と元の比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 二重随伴を元の全パラメータの同じ懸垂評価へ施した座標。 -/
def kanAdjointDoubleCounitCoordinate (n : ℕ)
    (d : (Y.level n).space ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Y.level (n + 2)).space)) :
    A ⟶ PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space))
      (Y.level (n + 2)).space :=
  kanAdjointStructureInput X Y φ n ≫
    PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (uncurry d) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u}
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space).inv

/-- 同じ元の構造区間の像は、通常と符号付き二重随伴の座標を結ぶ実際の区間。 -/
def kanAdjointDoubleCounitInterval (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space))
        (Y.level (n + 2)).space))
      (kanAdjointDoubleCounitCoordinate X Y φ n
        (KanSequence.ordinaryDoubleAdjoint Y.toKanSequence n))
      (kanAdjointDoubleCounitCoordinate X Y φ n
        (KanSequence.signedDoubleAdjoint Y.toKanSequence n)) :=
  (kanAdjointStructureCounitInterval X Y φ n).changeEndpoints
    (kanAdjointStructureCounit_source_double X Y φ n).symm
    (kanAdjointStructureCounit_target X Y φ n).symm

/-- 二重随伴の座標表示でも、元の選択済み構造区間の同じ辺を保持する。 -/
lemma kanAdjointDoubleCounitInterval_path (n : ℕ) :
    (kanAdjointDoubleCounitInterval X Y φ n).path =
      (kanAdjointStructureCounitInterval X Y φ n).path := rfl

/-- 全区間の射も、元の普遍係数逆区間の同じ入力と同じ counit の合成そのもの。 -/
lemma kanAdjointDoubleCounitInterval_h (n : ℕ) :
    (kanAdjointDoubleCounitInterval X Y φ n).homotopy.h =
      (kanAdjointStructureInput X Y φ n).right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointCoefficientReversePath X Y n).homotopy.h ≫
        (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space).right := by
  rw [kanAdjointDoubleCounitInterval,
    PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    kanAdjointStructureCounitInterval_h, kanAdjointParameterStructureInterval_h, Category.assoc]

/-- 任意の指定部分への制限も、同じ元の係数区間の制限として計算される。 -/
lemma kanAdjointDoubleCounitInterval_boundary {B : PointedSimplicialSet.{u}}
    (j : B ⟶ A) (n : ℕ) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫ (kanAdjointDoubleCounitInterval X Y φ n).homotopy.h =
      (j ≫ kanAdjointStructureInput X Y φ n).right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointCoefficientReversePath X Y n).homotopy.h ≫
        (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space).right := by
  rw [kanAdjointDoubleCounitInterval,
    PointedMapping.VerticalPath.changeEndpoints_homotopy_h]
  exact kanAdjointStructureCounitInterval_boundary X Y φ j n

/-- 部分パラメータで先に制限して構成しても、同じ実区間全体への制限に厳密に一致する。 -/
lemma kanAdjointDoubleCounitInterval_pre {B : PointedSimplicialSet.{u}}
    (j : B ⟶ A) (n : ℕ) :
    (kanAdjointDoubleCounitInterval X Y (j ≫ φ) n).homotopy.h =
      j.right ▷ (Δ[1] : SSet.{u}) ≫ (kanAdjointDoubleCounitInterval X Y φ n).homotopy.h := by
  rw [kanAdjointDoubleCounitInterval_h, kanAdjointDoubleCounitInterval_h]
  simp only [kanAdjointStructureInput, Under.comp_right, comp_whiskerRight, Category.assoc]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
