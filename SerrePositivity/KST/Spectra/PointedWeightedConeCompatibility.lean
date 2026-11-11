module

public import SerrePositivity.KST.Spectra.PointedWeightedCone
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeUnit

/-!
概要：点つき weighted end への標準比較は係数と内部 Hom に関して自然。
方針：各 end 射影を定数族で計算し、単位と二重 Hom の交換の整合性を使う。
規約：普通の点つき射の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。標準比較を Kan 列の厳密な射へ束ねる。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedConeCompatibilityPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I]

/-- 概要：内部 Hom と end の交換同型の各射影の式。
方針：内部 Hom の end 比較と二重 Hom の交換を成分で評価する。
規約：順射は loop から係数の loop の end へ向かう。
使われ方：HA §1.4.2。標準比較と loop 交換の整合性。 -/
@[reassoc]
theorem cotensorIso_π (A : PointedSimplicialSet.{u}) (W : I ⥤ SSet.{u})
    (D : I ⥤ PointedSimplicialSet.{u}) (i : I) :
    (cotensorIso A W D).hom ≫ end_.π (diagram W (D ⋙ ihom A)) i =
      (ihom A).map (end_.π (diagram W D) i) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (PointedObject.adjoin (W.obj i)) (D.obj i)).hom := by
  change (EndInternalHom.homToEnd A (diagram W D) ≫
    end_.map (cotensorDiagramIso A W D).hom) ≫ end_.π _ i = _
  rw [Category.assoc, end_.map_π, ← Category.assoc, EndInternalHom.homToEnd_π]
  rfl

/-- 概要：定数族は二つの内部 Hom の源の交換と整合する。
方針：重みを単位へ潰す射の自然性と単位の交換式を使う。
規約：重みの元の成分にわたる定数族。
使われ方：HA §1.4.2、BF 1978 §2。標準比較の loop との整合性。 -/
@[reassoc]
theorem constantFamily_exchange (A : PointedSimplicialSet.{u}) (B : SSet.{u})
    (Y : PointedSimplicialSet.{u}) :
    (ihom A).map (constantFamily B Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (PointedObject.adjoin B) Y).hom =
        constantFamily B ((ihom A).obj Y) := by
  rw [constantFamily, constantFamily, CategoryTheory.Functor.map_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.natural_unit_inv]

/-- 概要：点つき end への標準比較は錐の頂点と係数図式に自然。
方針：各射影で錐成分の可換式と定数族の標的自然性を使う。
規約：極限錐の仮定は不要。
使われ方：HA §1.4.2、BF 1978 §2。Kan 列の構造射との可換性。 -/
@[reassoc]
theorem coneComparison_natural (W : I ⥤ SSet.{u}) {D E : I ⥤ PointedSimplicialSet.{u}}
    (c : Cone D) (d : Cone E) (f : c.pt ⟶ d.pt) (τ : D ⟶ E)
    (h : ∀ i, f ≫ d.π.app i = c.π.app i ≫ τ.app i) :
    f ≫ coneComparison W d = coneComparison W c ≫ map W τ := by
  apply end_.hom_ext
  intro i
  have hl : (f ≫ coneComparison W d) ≫ end_.π (diagram W E) i =
      (f ≫ d.π.app i) ≫ constantFamily (W.obj i) (E.obj i) := by
    rw [Category.assoc, coneComparison_π, ← Category.assoc]
  have hr : (coneComparison W c ≫ map W τ) ≫ end_.π (diagram W E) i =
      (c.π.app i ≫ τ.app i) ≫ constantFamily (W.obj i) (E.obj i) := by
    rw [Category.assoc, map_π, ← Category.assoc, coneComparison_π,
      Category.assoc, constantFamily_post, ← Category.assoc]
  exact hl.trans ((congrArg (fun z ↦ z ≫ constantFamily (W.obj i) (E.obj i)) (h i)).trans hr.symm)

/-- 概要：標準比較を内部 Hom に送ってから end と交換すると、内部 Hom を施した錐の標準比較。
方針：各射影の定数族の式と二重 Hom 交換を使う。
規約：通常の点つき射の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。随伴構造射と標準比較の可換性。 -/
@[reassoc]
theorem coneComparison_cotensor (A : PointedSimplicialSet.{u}) (W : I ⥤ SSet.{u})
    {D : I ⥤ PointedSimplicialSet.{u}} (c : Cone D) :
    (ihom A).map (coneComparison W c) ≫ (cotensorIso A W D).hom =
      coneComparison W ((ihom A).mapCone c) := by
  apply end_.hom_ext
  intro i
  rw [Category.assoc, cotensorIso_π, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    coneComparison_π, CategoryTheory.Functor.map_comp, Category.assoc,
    constantFamily_exchange, coneComparison_π]
  rfl

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
