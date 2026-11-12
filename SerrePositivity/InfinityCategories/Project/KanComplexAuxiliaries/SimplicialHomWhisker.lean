module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-! # 元の通常射の豊穣表示と全 Hom の前後合成
概要：通常射の単位パラメータ表示に前後合成すると、同じ元の合成射を回収する。
方針：全単体で元の豊穣合成保存を評価する。
規約：対象の追加仮定なし。使われ方：実押し出しの通常射の厳密な回収。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
variable {D : Type v} [Category.{u} D] [SimplicialCategory D]

/-- 元の通常射の豊穣表示の後合成は、同じ合成射を回収する。 -/
lemma simplicialHom_post {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet f ≫ eHomWhiskerLeft SSet X g = eHomEquiv SSet (f ≫ g) := by
  ext n p
  change PUnit.{u + 1} at p
  have hp : p = PUnit.unit := Subsingleton.elim _ _
  subst p
  change (eComp SSet X Y Z).app n
    ((eHomEquiv SSet f).app n PUnit.unit, (eHomEquiv SSet g).app n PUnit.unit) = _
  exact (types_congr_hom (NatTrans.congr_app (eHomEquiv_comp SSet f g) n) PUnit.unit).symm

/-- 元の通常射の豊穣表示の前合成は、同じ合成射を回収する。 -/
lemma simplicialHom_pre {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet g ≫ eHomWhiskerRight SSet f Z = eHomEquiv SSet (f ≫ g) := by
  ext n p
  change PUnit.{u + 1} at p
  have hp : p = PUnit.unit := Subsingleton.elim _ _
  subst p
  change (eComp SSet X Y Z).app n
    ((eHomEquiv SSet f).app n PUnit.unit, (eHomEquiv SSet g).app n PUnit.unit) = _
  exact (types_congr_hom (NatTrans.congr_app (eHomEquiv_comp SSet f g) n) PUnit.unit).symm

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplicialHom_post := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialHom_post

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplicialHom_pre := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialHom_pre
