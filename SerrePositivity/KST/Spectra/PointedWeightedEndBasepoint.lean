module

public import SerrePositivity.KST.Spectra.PointedWeightedEndMap

/-!
概要：点つき end の基礎比較は各基点の定数族を表す。
方針：自由基点からの Hom の元の成分への制限を基点で計算し、end の射影を使う。
規約：通常の単体集合の end への基点の具体式。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。Tot と end の比較の基点保存。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory SSet

open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance endBasepointPointedEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 概要：自由基点からの内部 Hom の基点を制限すると通常の定数族になる。
方針：点つき Hom の包含で基点を計算し、curry と前合成を交換する。
規約：パラメーターは基礎単体集合のモノイダル単位。
使われ方：HA §1.4.2。end の基点の成分の計算。 -/
lemma FreePointedHomRestriction.basepoint_restrict (A : SSet.{u})
    (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom (PointedObject.adjoin A) Y).hom ≫ restrict A Y =
      curry (snd A (𝟙_ SSet.{u}) ≫ Y.hom) := by
  rw [restrict, ← Category.assoc, PointedObject.basedHom_basepoint_ι,
    PointedObject.homBasepoint, curry_pre_app, comp_toUnit_assoc]
  congr 1

namespace PointedWeightedEnd

variable {I : Type u} [SmallCategory I]

/-- 概要：点つき係数図式の各基点による厳密な錐。
方針：各点つき対象の基点を錐の成分とする。
規約：基礎図式への錐であり頂点は単位単体集合。
使われ方：Goerss–Jardine VIII §1。end と Tot の標準基点の表示。 -/
def basepointCone (D : I ⥤ PointedSimplicialSet.{u}) :
    Cone (D ⋙ PointedSimplicialSet.forget) where
  pt := 𝟙_ SSet.{u}
  π :=
    { app i := (D.obj i).hom
      naturality i j f := by
        change 𝟙 _ ≫ (D.obj j).hom = (D.obj i).hom ≫ (D.map f).right
        rw [Category.id_comp, Under.w] }

/-- 概要：点つき end の基点は忘却の比較の後で各係数の基点の定数族になる。
方針：各 end 射影と点つき射の基点保存を使う。
規約：通常の基礎単体集合の射の等式。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。密度比較の基点保存の入力。 -/
lemma underlyingIso_basepoint (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :
    (obj W D).hom ≫ (underlyingIso W D).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (basepointCone D) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, underlyingIso_π, ← Category.assoc, Under.w]
  change (PointedObject.basedHom (PointedObject.adjoin (W.obj i)) (D.obj i)).hom ≫
      FreePointedHomRestriction.restrict (W.obj i) (D.obj i) = _
  rw [FreePointedHomRestriction.basepoint_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π]
  rfl

end PointedWeightedEnd

end

end SerrePositivity.KST.Spectra
