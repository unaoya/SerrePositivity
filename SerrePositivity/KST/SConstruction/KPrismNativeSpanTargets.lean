module
public import SerrePositivity.KST.SConstruction.KPrismSliceDiagrams
public import SerrePositivity.KST.SConstruction.KPrismNativeSpanFamilies

/-! # 上下の元の K 円柱を元の suspension 写像空間へ戻す
概要：上下の円柱の標的を、元の K の段の suspension から次段への基点つき写像空間へ同定する。
方針：同じ元の頂点の等式のみを移し、元の族と実円柱を逆射で厳密に回収する。
規約：新しい代表や円柱を選ばず、元の次段の Kan 性から標的の Kan 性を得る。
使われ方：二円柱を元の二合成へ照合し、同じ標的内の相対合成へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismNativeSpanTargets_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の段の suspension から元の次段への、実際の基点つき写像空間。 -/
def kKanOriginalSuspensionMappingTarget {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x y : I) : SSet.{u} :=
  (PointedObject.basedHom
    (PointedSimplicialSet.circle.{u} ⊗ ((kKanSequence (F.obj x)).level r).space)
    ((kKanSequence (F.obj y)).level (r + 1)).space).right

/-- 同じ元の次段の Kan 性により、写像空間も Kan である。 -/
instance kKanOriginalSuspensionMappingTarget_kanComplex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x y : I) :
    KanComplex (kKanOriginalSuspensionMappingTarget r F x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の prism の native Hom を、元の suspension 写像空間へ対象の等式だけで同定する。 -/
def kKanOriginalPrismNativeHomIso {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x y : I) :
    SimplicialCategory.sHom
      (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (x, ULift.up 0))
      (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (y, ULift.up 1)) ≅
        kKanOriginalSuspensionMappingTarget r F x y :=
  eqToIso (congrArg₂ (fun A B : PointedSimplicialSet.{u} => (PointedObject.basedHom A B).right)
    (kKanOriginalPrismStringVertex_bottom r F x) (kKanOriginalPrismStringVertex_top r F y))

/-- 二円柱が共有する、元の長辺の値を同じ suspension 写像空間内に表示した頂点。 -/
def kKanOriginalPrismSpanInitialVertex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalSuspensionMappingTarget r F x y) _⦋0⦌ :=
  (kKanOriginalPrismNativeHomIso r F x y).hom.app (Opposite.op ⦋0⦌)
    (coherentArrowNativeInitialVertex (kKanOriginalPrismStringDiagram r F)
      (coherentPrismArrow f))

/-- 下側の元の全合成列族を、元の suspension 写像空間内に表示する。 -/
def kKanOriginalPrismLowerSuspensionFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⟶ kKanOriginalSuspensionMappingTarget r F x y :=
  kKanOriginalPrismLowerNativeFamily r F f ≫ (kKanOriginalPrismNativeHomIso r F x y).hom

/-- 元の suspension 写像空間内の、同じ長辺から下側の全合成列への実円柱。 -/
def kKanOriginalPrismLowerSuspensionContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy (SSet.const (kKanOriginalPrismSpanInitialVertex r F f))
      (kKanOriginalPrismLowerSuspensionFamily r F f) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (kKanOriginalPrismLowerNativeContraction r F f)
    (kKanOriginalPrismNativeHomIso r F x y).hom
  exact
    { h := H.h
      h₀ := H.h₀.trans (SSet.const_comp _ _)
      h₁ := H.h₁
      rel := H.rel }

/-- 対象の表示を戻すと、元の下側の全族を厳密に回収する。 -/
lemma kKanOriginalPrismLowerSuspensionFamily_recover {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismLowerSuspensionFamily r F f ≫ (kKanOriginalPrismNativeHomIso r F x y).inv =
      kKanOriginalPrismLowerNativeFamily r F f := by
  rw [kKanOriginalPrismLowerSuspensionFamily, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 対象の表示を戻すと、元の下側の実円柱も全時刻で厳密に回収する。 -/
lemma kKanOriginalPrismLowerSuspensionContraction_recover {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismLowerSuspensionContraction r F f).h ≫
      (kKanOriginalPrismNativeHomIso r F x y).inv =
        (kKanOriginalPrismLowerNativeContraction r F f).h := by
  change ((kKanOriginalPrismLowerNativeContraction r F f).h ≫
    (kKanOriginalPrismNativeHomIso r F x y).hom) ≫ _ = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 上側の元の全合成列族を、元の suspension 写像空間内に表示する。 -/
def kKanOriginalPrismUpperSuspensionFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⟶ kKanOriginalSuspensionMappingTarget r F x y :=
  kKanOriginalPrismUpperNativeFamily r F f ≫ (kKanOriginalPrismNativeHomIso r F x y).hom

/-- 元の suspension 写像空間内の、同じ長辺から上側の全合成列への実円柱。 -/
def kKanOriginalPrismUpperSuspensionContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy (SSet.const (kKanOriginalPrismSpanInitialVertex r F f))
      (kKanOriginalPrismUpperSuspensionFamily r F f) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (kKanOriginalPrismUpperNativeContraction r F f)
    (kKanOriginalPrismNativeHomIso r F x y).hom
  exact
    { h := H.h
      h₀ := H.h₀.trans (SSet.const_comp _ _)
      h₁ := H.h₁
      rel := H.rel }

/-- 対象の表示を戻すと、元の上側の全族を厳密に回収する。 -/
lemma kKanOriginalPrismUpperSuspensionFamily_recover {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismUpperSuspensionFamily r F f ≫ (kKanOriginalPrismNativeHomIso r F x y).inv =
      kKanOriginalPrismUpperNativeFamily r F f := by
  rw [kKanOriginalPrismUpperSuspensionFamily, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 対象の表示を戻すと、元の上側の実円柱も全時刻で厳密に回収する。 -/
lemma kKanOriginalPrismUpperSuspensionContraction_recover {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismUpperSuspensionContraction r F f).h ≫
      (kKanOriginalPrismNativeHomIso r F x y).inv =
        (kKanOriginalPrismUpperNativeContraction r F f).h := by
  change ((kKanOriginalPrismUpperNativeContraction r F f).h ≫
    (kKanOriginalPrismNativeHomIso r F x y).hom) ≫ _ = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.KST.SConstruction
