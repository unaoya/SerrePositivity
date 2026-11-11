module
public import SerrePositivity.KST.SConstruction.PointedSSetObject
public import SerrePositivity.KST.SConstruction.PointedFamilyPost

/-! # 標準点つき豊穣の前後合成と元の basedHom
概要：専用の標準点つき対象の前後合成を、元の点つき写像族の前後合成と同定する。
方針：同じ Hom・単位・合成で移した豊穣の定義を使う。
規約：大域 instance を変更しない。使われ方：元の S₁ 比較の厳密豊穣自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 標準点つき豊穣の後合成は、同じ元の basedHom の後合成。 -/
lemma pointedSSetObject_whiskerLeft (X : PointedSSetObject.{u})
    {Y Z : PointedSSetObject.{u}} (f : Y ⟶ Z) :
    eHomWhiskerLeft SSet X f = pointedFamilyPost X.obj Y.obj Z.obj f :=
  Spectra.PointedEnrichment.whiskerLeft_eq X.obj f

/-- 標準点つき豊穣の前合成は、同じ元の basedHom の前合成。 -/
lemma pointedSSetObject_whiskerRight {X Y : PointedSSetObject.{u}} (f : X ⟶ Y)
    (Z : PointedSSetObject.{u}) :
    eHomWhiskerRight SSet f Z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z.obj :=
  Spectra.PointedEnrichment.whiskerRight_eq f Z.obj

end SerrePositivity.KST.SConstruction
