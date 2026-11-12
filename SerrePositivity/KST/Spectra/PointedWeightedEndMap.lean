module

public import SerrePositivity.KST.Spectra.PointedWeightedEnd

/-!
概要：点つき enriched end の係数の射と underlying end との自然な比較。
方針：各射影の後合成を end へ持ち上げ、自由基点の制限の自然性で基礎の図式に比較する。
規約：全て実際の点つき射として構成する。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の随伴構造射を end に送る。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet Opposite

open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedEndMapSelfEnrichment : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  enrichedOrdinaryCategorySelf SSet.{u}

local instance weightedEndMapPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I]

/-- 概要：点つき end の射影は閉構造の源制限と標的後合成で整合する。
方針：enriched end の条件を通常の内部 Hom の射に書き直す。
規約：重みの自由基点を加えた射で制限する。
使われ方：HA §1.4.2。係数の射を end へ持ち上げる整合条件。 -/
theorem π_condition (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u})
    {i j : I} (f : i ⟶ j) :
    end_.π (diagram W D) i ≫ (ihom (PointedObject.adjoin (W.obj i))).map (D.map f) =
      end_.π (diagram W D) j ≫
        (pre (PointedObject.adjoinFunctor.map (W.map f))).app (D.obj j) := by
  have h := end_.condition (diagram W D) f
  change end_.π (diagram W D) i ≫
      eHomWhiskerLeft PointedSimplicialSet.{u} (PointedObject.adjoin (W.obj i)) (D.map f) =
    end_.π (diagram W D) j ≫ eHomWhiskerRight PointedSimplicialSet.{u}
      (PointedObject.adjoinFunctor.map (W.map f)) (D.obj j) at h
  rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
  exact h

/-- 概要：係数図式の自然変換が点つき end に誘導する実際の射。
方針：各 end 射影へ内部 Hom の後合成を施して持ち上げる。
規約：通常の点つき射の厳密な構成。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の構造射と射への作用。 -/
def map (W : I ⥤ SSet.{u}) {D E : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) :
    obj W D ⟶ obj W E :=
  end_.lift (fun i ↦ end_.π (diagram W D) i ≫
    (ihom (PointedObject.adjoin (W.obj i))).map (τ.app i)) (fun i j f ↦ by
      change (end_.π (diagram W D) i ≫
          (ihom (PointedObject.adjoin (W.obj i))).map (τ.app i)) ≫
            eHomWhiskerLeft PointedSimplicialSet.{u}
              (PointedObject.adjoin (W.obj i)) (E.map f) =
        (end_.π (diagram W D) j ≫
          (ihom (PointedObject.adjoin (W.obj j))).map (τ.app j)) ≫
            eHomWhiskerRight PointedSimplicialSet.{u}
              (PointedObject.adjoinFunctor.map (W.map f)) (E.obj j)
      rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
        enrichedOrdinaryCategorySelf_eHomWhiskerRight]
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← τ.naturality f,
        CategoryTheory.Functor.map_comp, ← Category.assoc, π_condition W D f, Category.assoc]
      erw [pre_comm_ihom_map]
      rw [← Category.assoc]
      rfl)

/-- 概要：係数の end 射は各射影で内部 Hom の後合成。
方針：end の持ち上げの成分式を使う。
規約：点つき射の等式。
使われ方：HA §1.4.2。係数の射の計算。 -/
@[reassoc (attr := simp)]
theorem map_π (W : I ⥤ SSet.{u}) {D E : I ⥤ PointedSimplicialSet.{u}}
    (τ : D ⟶ E) (i : I) :
    map W τ ≫ end_.π (diagram W E) i = end_.π (diagram W D) i ≫
      (ihom (PointedObject.adjoin (W.obj i))).map (τ.app i) :=
  end_.lift_π _ _ i

/-- 概要：underlying end の比較同型は各射影で自由基点の元の成分への制限。
方針：忘却と end の交換、および図式の同型の end 射の成分式を使う。
規約：通常の単体集合の厳密な等式。
使われ方：HA §1.4.2。Kan end の比較の自然性。 -/
@[reassoc]
theorem underlyingIso_π (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) (i : I) :
    (underlyingIso W D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (D ⋙ PointedSimplicialSet.forget) i =
      (end_.π (diagram W D) i).right ≫ FreePointedHomRestriction.restrict (W.obj i) (D.obj i) := by
  change (EndRightAdjoint.toEnd (R := PointedSimplicialSet.forget) (diagram W D) ≫
      end_.map (underlyingDiagramIso W D).hom) ≫ end_.π _ i = _
  rw [Category.assoc, end_.map_π, ← Category.assoc, EndRightAdjoint.toEnd_π]
  rfl

/-- 概要：underlying end の比較は係数の自然変換に関して自然。
方針：各射影で end 射と自由基点の制限の自然性を比較する。
規約：通常の単体集合の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。π_* 同型保存の点つき模型への移送。 -/
@[reassoc]
theorem underlyingIso_natural (W : I ⥤ SSet.{u}) {D E : I ⥤ PointedSimplicialSet.{u}}
    (τ : D ⟶ E) :
    (map W τ).right ≫ (underlyingIso W E).hom =
      (underlyingIso W D).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W (Functor.whiskerRight τ PointedSimplicialSet.forget) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, underlyingIso_π, ← Category.assoc]
  have hp := congrArg Under.Hom.right (map_π W τ i)
  change (map W τ).right ≫ (end_.π (diagram W E) i).right =
    (end_.π (diagram W D) i).right ≫
      (PointedObject.basedHomMap (PointedObject.adjoin (W.obj i)) (τ.app i)).right at hp
  rw [hp, Category.assoc, FreePointedHomRestriction.natural_post]
  conv_rhs => rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π, ← Category.assoc, underlyingIso_π]
  rfl

/-- 概要：点つき Bousfield–Kan enriched end は全基点 π_* 同型を保つ。
方針：基礎の Kan end の同型不変性を自然な比較同型で共役する。
規約：L9 の全基点・零次数を含む π_* 同型を用いる。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の Ω 条件の保存。 -/
theorem map_piIsomorphism {D E : I ⥤ PointedSimplicialSet.{u}}
    [∀ i, KanComplex (D.obj i).right] [∀ i, KanComplex (E.obj i).right]
    (τ : D ⟶ E) (hτ : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (τ.app i).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) τ).right := by
  let : ∀ i, KanComplex ((D ⋙ PointedSimplicialSet.forget).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (D.obj i).right)
  let : ∀ i, KanComplex ((E ⋙ PointedSimplicialSet.forget).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (E.obj i).right)
  let eD := underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D
  let eE := underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) E
  have heD : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism eD.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso eD
  have heE : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism eE.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso eE
  have hN := PointedHomotopyLimit.map_piIsomorphism τ hτ
  have hc := heD.comp hN
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := eE.hom) _ heE
  have h := underlyingIso_natural (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) τ
  change (map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) τ).right ≫ eE.hom =
    eD.hom ≫ (PointedHomotopyLimit.map τ).right at h
  rw [h]
  exact hc

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
