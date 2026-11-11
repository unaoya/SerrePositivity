module

public import SerrePositivity.KST.Spectra.PointedWeightedEndMap
public import SerrePositivity.KST.Spectra.PointedWeightedEndCotensor

/-!
概要：点つき図式の厳密な錐から重み付き end への標準比較射。
方針：自由基点の元の成分を忘れて定数な族を作り、end へ持ち上げる。
規約：極限錐の仮定を要求しない実際の点つき射。
使われ方：HA §1.4.2、BF 1978 §2、Kerodon 7.5.4.1（Tag 03B6）。有理自明作用の標準比較の入力。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedConePointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 概要：自由基点の元の成分を一点へ潰す点つき射。
方針：終対象への射へ自由基点追加を施す。
規約：終域は smash の単位である零次球面。
使われ方：HA §1.4.2。重みの変数を忘れた定数族の定義。 -/
def weightCollapse (A : SSet.{u}) : PointedObject.adjoin A ⟶ 𝟙_ PointedSimplicialSet.{u} :=
  PointedObject.adjoinFunctor.map (toUnit A)

/-- 概要：重みの変数を潰す射は源に関して自然。
方針：自由基点追加の合成保存と終対象の一意性を使う。
規約：任意の単体集合の射。
使われ方：HA §1.4.2。end の成分の整合性。 -/
@[reassoc]
theorem weightCollapse_natural {A B : SSet.{u}} (f : A ⟶ B) :
    PointedObject.adjoinFunctor.map f ≫ weightCollapse B = weightCollapse A := by
  change PointedObject.adjoinFunctor.map f ≫ PointedObject.adjoinFunctor.map (toUnit B) =
    PointedObject.adjoinFunctor.map (toUnit A)
  rw [← CategoryTheory.Functor.map_comp, comp_toUnit]

/-- 概要：点つき対象の元を重み全体で定数な族へ送る点つき射。
方針：単位からの内部 Hom の逆同型に重みを潰す射の前合成を施す。
規約：新しく加えた基点では常に基点。
使われ方：HA §1.4.2、BF 1978 §2。厳密な錐から end への標準比較。 -/
def constantFamily (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    Y ⟶ (ihom (PointedObject.adjoin A)).obj Y :=
  (unitIsoSelf (X := Y)).inv ≫ (pre (weightCollapse A)).app Y

/-- 概要：定数族の構成は標的の点つき射と可換。
方針：pre の標的自然性と単位の内部 Hom の自然性を使う。
規約：点つき射の厳密な等式。
使われ方：HA §1.4.2。標準比較射の係数の自然性。 -/
@[reassoc]
theorem constantFamily_post (A : SSet.{u}) {Y Z : PointedSimplicialSet.{u}} (f : Y ⟶ Z) :
    constantFamily A Y ≫ (ihom (PointedObject.adjoin A)).map f = f ≫ constantFamily A Z := by
  rw [constantFamily, constantFamily, Category.assoc, pre_comm_ihom_map, ← Category.assoc]
  have h := (unitNatIso (C := PointedSimplicialSet.{u})).hom.naturality f
  change f ≫ (unitIsoSelf (X := Z)).inv =
    (unitIsoSelf (X := Y)).inv ≫ (ihom (𝟙_ PointedSimplicialSet.{u})).map f at h
  rw [← h, Category.assoc]

/-- 概要：定数族は重みの源の射で制限しても同じ定数族。
方針：前合成の合成則と重みを潰す射の自然性を使う。
規約：点つき射の厳密な等式。
使われ方：HA §1.4.2。end の射の自然性の整合条件。 -/
@[reassoc]
theorem constantFamily_pre {A B : SSet.{u}} (f : A ⟶ B) (Y : PointedSimplicialSet.{u}) :
    constantFamily B Y ≫ (pre (PointedObject.adjoinFunctor.map f)).app Y = constantFamily A Y := by
  rw [constantFamily, constantFamily, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    weightCollapse_natural]

variable {I : Type u} [SmallCategory I]

/-- 概要：点つき図式の錐から重み付き end への標準射。
方針：各錐成分に定数族の射を後合成して end に持ち上げる。
規約：錐の極限性は仮定しない。
使われ方：HA §1.4.2、BF 1978 §2、Kerodon 7.5.4.1（Tag 03B6）。自明作用から hG への比較。 -/
def coneComparison (W : I ⥤ SSet.{u}) {D : I ⥤ PointedSimplicialSet.{u}} (c : Cone D) :
    c.pt ⟶ obj W D :=
  end_.lift (fun i ↦ c.π.app i ≫ constantFamily (W.obj i) (D.obj i)) (fun i j f ↦ by
    change (c.π.app i ≫ constantFamily (W.obj i) (D.obj i)) ≫
        eHomWhiskerLeft PointedSimplicialSet.{u} (PointedObject.adjoin (W.obj i)) (D.map f) =
      (c.π.app j ≫ constantFamily (W.obj j) (D.obj j)) ≫
        eHomWhiskerRight PointedSimplicialSet.{u}
          (PointedObject.adjoinFunctor.map (W.map f)) (D.obj j)
    rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      enrichedOrdinaryCategorySelf_eHomWhiskerRight, Category.assoc,
      constantFamily_post, ← Category.assoc]
    have hc : c.π.app i ≫ D.map f = c.π.app j := c.w f
    rw [hc, Category.assoc]
    erw [constantFamily_pre])

/-- 概要：標準比較射の各 end 射影は錐成分の定数族。
方針：end の持ち上げの式を使う。
規約：厳密な点つき射の等式。
使われ方：HA §1.4.2。標準比較の π_* を検査する成分の公式。 -/
@[reassoc (attr := simp)]
theorem coneComparison_π (W : I ⥤ SSet.{u}) {D : I ⥤ PointedSimplicialSet.{u}}
    (c : Cone D) (i : I) :
    coneComparison W c ≫ end_.π (diagram W D) i = c.π.app i ≫ constantFamily (W.obj i) (D.obj i) :=
  end_.lift_π _ _ i

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
