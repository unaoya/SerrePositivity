module
public import SerrePositivity.KST.SConstruction.CoherentPrismNativeFamilies
public import SerrePositivity.KST.SConstruction.KPrismNativeStringFamilies

/-! # 元の K prism から供給する上下の実円柱
概要：元の各段の K prism から、共通の全合成列パラメータ上に二つの実円柱を構成する。
方針：同じ元の通常積圏表示を上下の列の関手で評価する。
規約：円柱を追加入力せず、全段と元の基点つき native Hom を保持する。
使われ方：二つの元の合成の照合と、BF 厳密化への境界一致の供給。
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
local instance kPrismNativeSpanFamilies_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の全段の K prism の、下側の全合成列の native Hom 族。 -/
def kKanOriginalPrismLowerNativeFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :=
  coherentPrismLowerNativeFamily (kKanOriginalPrismStringDiagram r F) f

/-- 元の K prism の同じ長辺から下側の全合成列へ向かう、共通パラメータ上の実円柱。 -/
def kKanOriginalPrismLowerNativeContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy
      (SSet.const (coherentArrowNativeInitialVertex (kKanOriginalPrismStringDiagram r F)
        (coherentPrismArrow f))) (kKanOriginalPrismLowerNativeFamily r F f) :=
  coherentPrismLowerNativeContraction (kKanOriginalPrismStringDiagram r F) f

/-- 元の K 実円柱の同じ収縮の厳密な制限であり、別の代表を選んでいない。 -/
lemma kKanOriginalPrismLowerNativeContraction_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismLowerNativeContraction r F f).h =
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanOriginalPrismNativeContraction r F (coherentPrismArrow f)).h := rfl

/-- 元の全段の K prism の、上側の全合成列の native Hom 族。 -/
def kKanOriginalPrismUpperNativeFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :=
  coherentPrismUpperNativeFamily (kKanOriginalPrismStringDiagram r F) f

/-- 元の K prism の同じ長辺から上側の全合成列へ向かう、共通パラメータ上の実円柱。 -/
def kKanOriginalPrismUpperNativeContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy
      (SSet.const (coherentArrowNativeInitialVertex (kKanOriginalPrismStringDiagram r F)
        (coherentPrismArrow f))) (kKanOriginalPrismUpperNativeFamily r F f) :=
  coherentPrismUpperNativeContraction (kKanOriginalPrismStringDiagram r F) f

/-- 元の K 実円柱の同じ収縮の厳密な制限であり、別の代表を選んでいない。 -/
lemma kKanOriginalPrismUpperNativeContraction_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismUpperNativeContraction r F f).h =
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanOriginalPrismNativeContraction r F (coherentPrismArrow f)).h := rfl

end SerrePositivity.KST.SConstruction
