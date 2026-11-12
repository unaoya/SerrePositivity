module
public import SerrePositivity.KST.Spectra.PointedEnrichment
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.KST.Spectra.PointedKanReplacement

/-! # 点つき Kan 複体の豊穣圏と coherent な図式
概要：構造射の自然性を扱う値域を、点つき Kan 複体の局所 Kan な豊穣圏で構成する。
方針：点つき単体集合の既存の豊穣構造を Kan な対象の全部分圏へ制限する。
規約：写像空間は基点を固定する実際の basedHom。通常の射は商にしない。
使われ方：L1d の比較の図式全体での反転と、スペクトル値の関手性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 点つき単体集合の基礎複体が Kan であるという対象条件。 -/
def pointedKanProperty : ObjectProperty PointedSimplicialSet.{u} :=
  fun X => KanComplex X.right

/-- 点つき Kan 複体の通常の全部分圏。 -/
abbrev PointedKanObject := pointedKanProperty.{u}.FullSubcategory

local instance pointedKanUnderlying_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 点つき Kan 複体の全部分圏は、元の基点固定写像空間で豊穣化される。 -/
instance pointedKanObject_simplicialCategory : SimplicialCategory PointedKanObject.{u} :=
  inferInstance

/-- 束ねた対象の基礎単体集合は Kan。 -/
instance pointedKanObject_kanComplex (X : PointedKanObject.{u}) : KanComplex X.obj.right := X.property

/-- 元の点つき写像空間との厳密な一致。 -/
lemma pointedKanObject_hom_eq (X Y : PointedKanObject.{u}) :
    SimplicialCategory.sHom X Y = (PointedObject.basedHom X.obj Y.obj).right := rfl

/-- 豊穣 Hom は基点固定写像空間の Kan 性によって Kan。 -/
instance pointedKanObject_sHom_kanComplex (X Y : PointedKanObject.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex X.obj Y.obj

/-- 点つき Kan 複体の coherent nerve。 -/
def PointedKanInfinity : SSet.{u + 1} := SimplicialNerve PointedKanObject.{u}

/-- 点つき Kan 複体の coherent nerve は追加仮定なしに ∞ 圏。 -/
instance pointedKanInfinity_quasicategory : Quasicategory PointedKanInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory PointedKanObject.{u}

/-- Kan 値の点つき図式を、同じ対象・射のまま全部分圏へ束ねる。 -/
def pointedKanDiagram {I : Type u} [SmallCategory I] (F : I ⥤ PointedSimplicialSet.{u})
    (hF : ∀ i, KanComplex (F.obj i).right) : I ⥤ PointedKanObject.{u} :=
  pointedKanProperty.lift F hF

/-- 束ねた図式を忘れると元の図式そのもの。 -/
lemma pointedKanDiagram_forget {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right) :
    pointedKanDiagram F hF ⋙ pointedKanProperty.ι = F := rfl

/-- 通常の Kan 値点つき図式を、全有限射列を持つ coherent な図式にする。 -/
def pointedKanCoherentDiagram {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PointedKanInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointedKanDiagram F hF)

/-- 点つき Kan 置換は全部分圏に値を持つ通常の関手。 -/
def pointedKanReplacementObjectFunctor : PointedSimplicialSet.{u} ⥤ PointedKanObject.{u} :=
  pointedKanProperty.lift PointedKanReplacement.functor (fun X => PointedKanReplacement.obj_kanComplex X)

end SerrePositivity.KST.SConstruction
