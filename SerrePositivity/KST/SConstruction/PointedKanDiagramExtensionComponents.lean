module
public import SerrePositivity.KST.SConstruction.PointedKanDiagramInverseTriangles
public import SerrePositivity.KST.SConstruction.PointedKanDiagramExtensions
public import SerrePositivity.KST.SConstruction.PointedExtensionHomotopy
public import SerrePositivity.KST.Spectra.PointedComponentIsomorphism

/-! # coherent な全体延長と元の厳密な Kan 延長の成分照合
概要：全入力単体で選んだ延長の成分が、元の任意の厳密な点つき延長と一致する。
方針：標的 Kan 単位との合成を計算し、anodyne 延長の一意性と全基点 π 同型を使う。
規約：元の延長を固定したまま比較し、図式全体の代表を選び直さない。
使われ方：全体の組み立て変換を既存の Kan 延長の選択へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 標的の Kan 単位の全体逆から回収した、元の Kan 模型への実際の射。 -/
def pointedKanDiagramUnitInverseMapAt {I : Type u} [SmallCategory I]
    (L : I ⥤ PointedSimplicialSet.{u}) (hL : ∀ i, KanComplex (L.obj i).right) (i : I) :
    (L ⋙ PointedKanReplacement.functor).obj i ⟶ L.obj i :=
  pointedKanDiagramHomotopyMapAt (pointedDiagramReplacement_isKan L) hL
    (pointedKanDiagramUnitInverseHomotopy L hL) i

/-- 回収した単位の全体逆は、元の単位の右逆の成分を持つ。 -/
lemma pointedKanDiagramUnitInverse_right_component {I : Type u} [SmallCategory I]
    (L : I ⥤ PointedSimplicialSet.{u}) (hL : ∀ i, KanComplex (L.obj i).right) (i : I) :
    componentOf (pointedKanDiagramUnitInverseMapAt L hL i ≫
      PointedKanReplacement.unit.app (L.obj i)) =
        componentOf (𝟙 ((L ⋙ PointedKanReplacement.functor).obj i)) := by
  exact pointedKanDiagramInverse_right_component hL (pointedDiagramReplacement_isKan L)
    (Functor.whiskerLeft L PointedKanReplacement.unit) (fun j => by
      let : KanComplex (L.obj j).right := hL j
      exact PointedKanReplacement.unit_piIsomorphism (L.obj j)) i

/-- 全体の coherent な延長から回収した元の Kan 模型間の射。 -/
def pointedKanDiagramExtensionMapAt {I : Type u} [SmallCategory I]
    {R L : I ⥤ PointedSimplicialSet.{u}} (hL : ∀ i, KanComplex (L.obj i).right)
    (θ : R ⟶ L) (i : I) : (R ⋙ PointedKanReplacement.functor).obj i ⟶ L.obj i :=
  pointedKanDiagramHomotopyMapAt (pointedDiagramReplacement_isKan R) hL
    (pointedKanDiagramExtensionHomotopy hL θ) i

/-- 全体延長の成分と標的の Kan 単位の合成は、元の変換の Kan 置換と同じ成分。 -/
lemma pointedKanDiagramExtension_post_unit_component {I : Type u} [SmallCategory I]
    {R L : I ⥤ PointedSimplicialSet.{u}} (hL : ∀ i, KanComplex (L.obj i).right)
    (θ : R ⟶ L) (i : I) :
    componentOf (pointedKanDiagramExtensionMapAt hL θ i ≫
      PointedKanReplacement.unit.app (L.obj i)) = componentOf (PointedKanReplacement.map (θ.app i)) := by
  have ht := pointedKanDiagramTriangle_components (pointedDiagramReplacement_isKan R)
    (pointedDiagramReplacement_isKan L) hL _ _ _ (pointedKanDiagramExtensionTriangle hL θ) i
  dsimp only [pointedKanReplacedNatTransHomotopy] at ht
  rw [pointedKanDiagramHomotopyMapAt_natTrans] at ht
  change componentOf (PointedKanReplacement.map (θ.app i) ≫ pointedKanDiagramUnitInverseMapAt L hL i) =
    componentOf (pointedKanDiagramExtensionMapAt hL θ i) at ht
  have hp := componentOf_comp_right ht (PointedKanReplacement.unit.app (L.obj i))
  have hi := componentOf_comp_left (pointedKanDiagramUnitInverse_right_component L hL i)
    (PointedKanReplacement.map (θ.app i))
  simp only [Category.assoc, Category.comp_id] at hp hi
  exact hp.symm.trans hi

/-- 全体で選んだ延長は、元の任意の厳密な Kan 延長と同じ点つき成分。 -/
lemma pointedKanDiagramExtensionMapAt_component {I : Type u} [SmallCategory I]
    {R L : I ⥤ PointedSimplicialSet.{u}} (hL : ∀ i, KanComplex (L.obj i).right)
    (θ : R ⟶ L) (i : I) (a : (R ⋙ PointedKanReplacement.functor).obj i ⟶ L.obj i)
    (ha : PointedKanReplacement.unit.app (R.obj i) ≫ a = θ.app i) :
    componentOf a = componentOf (pointedKanDiagramExtensionMapAt hL θ i) := by
  let : KanComplex (L.obj i).right := hL i
  let j : L.obj i ⟶ PointedKanReplacement.obj (L.obj i) :=
    PointedKanReplacement.unit.app (L.obj i)
  have hs : componentOf (a ≫ j) = componentOf (PointedKanReplacement.map (θ.app i)) := by
    obtain ⟨e⟩ := pointedExtensions_nonempty_mappingEdge
      (A := R.obj i) (B := PointedKanReplacement.obj (R.obj i))
      (Z := PointedKanReplacement.obj (L.obj i))
      (PointedKanReplacement.unit.app (R.obj i)) (PointedKanReplacement.unit_anodyne (R.obj i))
      (θ.app i ≫ j) (a ≫ j) (PointedKanReplacement.map (θ.app i))
      (by rw [← Category.assoc, ha]) (by
        have hn := (PointedKanReplacement.unit.naturality (θ.app i)).symm
        change PointedKanReplacement.unit.app (R.obj i) ≫ PointedKanReplacement.map (θ.app i) =
          θ.app i ≫ PointedKanReplacement.unit.app (L.obj i) at hn
        exact hn)
    exact SSet.π₀.sound e
  apply componentOf_cancel_post_piIsomorphism
    (X := L.obj i) (Y := PointedKanReplacement.obj (L.obj i)) j (PointedKanReplacement.unit_piIsomorphism (L.obj i))
  exact hs.trans (pointedKanDiagramExtension_post_unit_component hL θ i).symm

end SerrePositivity.KST.SConstruction
