module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitWedge

/-!
概要：元の段ごとの homotopy end の wedge への普遍射を Kan 列の射として構成する。
方針：各段の end の普遍射を取り、loop 交換の射影公式で構造可換性を示す。
規約：元の wedge への厳密な普遍射。使われ方：小図式の homotopy end の極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite

namespace SerrePositivity.KST.Spectra.KanSequence
local instance homotopyWedgeSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I] (D : I ⥤ KanSequence.{u})
  (s : Wedge (weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D))

/-- 任意の Kan 列の wedge の各段は、点つき end の整合族である。 -/
lemma homotopyLimitWedgeFamily_condition (n : ℕ) {i j : I} (f : i ⟶ j) :
    (s.ι i).app n ≫
        ((PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n)).obj (op i)).map f =
      (s.ι j).app n ≫
        ((PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (levelDiagram D n)).map f.op).app j := by
  have h := congrArg (fun p ↦ p.app n) (Wedge.condition s f)
  change (s.ι i).app n ≫
      (ihom (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i))).map ((D.map f).app n) =
    (s.ι j).app n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
      (PointedObject.adjoinFunctor.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).map f)) _ at h
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  dsimp only [PointedWeightedEnd.diagram, Enriched.FunctorCategory.diagram,
    eHomFunctor, Functor.comp, Functor.op, Functor.whiskeringLeft, Functor.whiskeringRight]
  simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight]
  exact h

/-- wedge から元の homotopy end への各段の普遍射。 -/
def homotopyLimitWedgeLiftApp (n : ℕ) :
    (s.pt.level n).space ⟶ ((homotopyLimit D).level n).space :=
  end_.lift (fun i ↦ (s.ι i).app n) (fun _ _ f ↦ homotopyLimitWedgeFamily_condition D s n f)

@[reassoc (attr := simp)]
lemma homotopyLimitWedgeLiftApp_π (n : ℕ) (i : I) :
    homotopyLimitWedgeLiftApp D s n ≫
        end_.π (PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n)) i =
      (s.ι i).app n := end_.lift_π _ _ _

/-- 段ごとの普遍射は homotopy end の実際の Ω 随伴と可換。 -/
lemma homotopyLimitWedgeLiftApp_adjoint (n : ℕ) :
    homotopyLimitWedgeLiftApp D s n ≫ homotopyLimitAdjoint D n =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (s.pt.sigma n) ≫
        (ihom PointedSimplicialSet.circle.{u}).map (homotopyLimitWedgeLiftApp D s (n + 1)) := by
  let A := PointedSimplicialSet.circle.{u}
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I
  let e := PointedWeightedEnd.cotensorIso A W (levelDiagram D (n + 1))
  apply (cancel_mono e.hom).mp
  apply end_.hom_ext
  intro i
  change ((homotopyLimitWedgeLiftApp D s n ≫ homotopyLimitAdjoint D n) ≫ e.hom) ≫
      end_.π (PointedWeightedEnd.diagram W (levelDiagram D (n + 1) ⋙ ihom A)) i = _
  conv_lhs =>
    dsimp only [homotopyLimitAdjoint, e, A, W]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [PointedWeightedEnd.map_π, ← Category.assoc, homotopyLimitWedgeLiftApp_π]
  conv_rhs =>
    rw [Category.assoc, Category.assoc,
      PointedWeightedEnd.cotensorIso_π A W (levelDiagram D (n + 1)) i]
    rw [← Category.assoc ((ihom A).map (homotopyLimitWedgeLiftApp D s (n + 1)))
      ((ihom A).map (end_.π (PointedWeightedEnd.diagram W (levelDiagram D (n + 1))) i))]
    rw [← CategoryTheory.Functor.map_comp, homotopyLimitWedgeLiftApp_π]
  have hs : (s.ι i).app n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv
      ((mapping (PointedObject.adjoin (W.obj i)) (D.obj i)).level n).space
      ((mapping (PointedObject.adjoin (W.obj i)) (D.obj i)).level (n + 1)).space
      ((mapping (PointedObject.adjoin (W.obj i)) (D.obj i)).sigma n) =
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (s.pt.sigma n) ≫
          (ihom A).map ((s.ι i).app (n + 1)) := (s.ι i).adjoint_comm n
  have h := congrArg (fun p ↦ p ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (PointedObject.adjoin (W.obj i))
        ((D.obj i).level (n + 1)).space).hom) hs
  rw [mapping_adjoint] at h
  simp only [Category.assoc] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv (PointedObject.adjoin (W.obj i)) A
    ((D.obj i).level (n + 1)).space, Iso.inv_hom_id] at h
  simp only [Category.comp_id] at h
  exact h

/-- 任意の重み付き wedge から元の homotopy end の列への厳密な普遍射。 -/
def homotopyLimitWedgeLift : s.pt ⟶ homotopyLimit D where
  app := homotopyLimitWedgeLiftApp D s
  comm n := by
    apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _).injective
    change curry (PointedSimplicialSet.circle.{u} ◁ homotopyLimitWedgeLiftApp D s n ≫
        (homotopyLimit D).sigma n) =
      curry (s.pt.sigma n ≫ homotopyLimitWedgeLiftApp D s (n + 1))
    rw [curry_natural_left, curry_natural_right]
    change homotopyLimitWedgeLiftApp D s n ≫ curry (uncurry (homotopyLimitAdjoint D n)) = _
    rw [curry_uncurry]
    exact homotopyLimitWedgeLiftApp_adjoint D s n

end SerrePositivity.KST.Spectra.KanSequence
