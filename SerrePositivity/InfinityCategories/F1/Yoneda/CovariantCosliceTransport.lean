module

public import SerrePositivity.InfinityCategories.F1.Yoneda.CovariantCosliceClassification
public import SerrePositivity.InfinityCategories.F1.Transport.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePointCoslice

/-!
概要：大きい底の表示上で作った表現可能な全空間比較を、小さい底の分類へ戻す。
方針：底の同型、全 coslice の宇宙同型、unstraightening の引き戻しを合成する。
規約：比較射の底は厳密に保持する。
使われ方：対象宇宙だけを持ち上げた単体的圏から元の共変 Hom 図式への帰還。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底の同型で表示した coslice の全空間同値から、元の小さい底上の全図式同型を得る。 -/
def covariantHomIsoOfDisplayedCosliceEquivalence
    {B : SSet.{u}} [Quasicategory B] {C : SSet.{u + 1}} [Quasicategory C]
    (e : C ≅ (SSet.uliftFunctor.{u + 1, u}).obj B)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : C ⟶ SpaceInfinity.{u}) (hg : e.hom ≫ F = G)
    (x : C _⦋0⦌) (b : B _⦋0⦌) (hb : e.hom.app (Opposite.op ⦋0⦌) x = ULift.up b)
    (f : sliceUnder (SSet.yonedaEquiv.symm x) ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = sliceUnderProjection (SSet.yonedaEquiv.symm x))
    (he : IsPrecompositionEquivalence f) : FunctorIso F (homInfinityCovariant b) := by
  let a := pointCoslicePostIso e x ≪≫
    eqToIso (congrArg (fun z => sliceUnder (SSet.yonedaEquiv.symm z)) hb)
  have ha : a.hom ≫ sliceUnderProjection
      ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{u + 1, u}).obj B)).symm (ULift.up b)) =
      sliceUnderProjection (SSet.yonedaEquiv.symm x) ≫ e.hom := by
    dsimp only [a, Iso.trans_hom, eqToIso.hom]
    rw [Category.assoc, sliceUnder_eqToHom_projection
      (congrArg SSet.yonedaEquiv.symm hb)]
    exact pointCoslicePostIso_projection e x
  have hai : a.inv ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x) ≫ e.hom =
      sliceUnderProjection
        ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{u + 1, u}).obj B)).symm (ULift.up b)) := by
    rw [← ha, ← Category.assoc, a.inv_hom_id, Category.id_comp]
  let g := leftUnstraighteningMap G F e.hom hg
  have gi : IsIso g := (leftUnstraighteningMap_isPullback G F e.hom hg).isIso_fst_of_isIso
  let k := (HomotopyLimits.pointCosliceUniverseIso.{u, u + 1} b).hom ≫ a.inv ≫ f ≫ g
  have kp : k ≫ leftUnstraighteningProjection F =
      (SSet.uliftFunctor.{u + 1, u}).map (sliceUnderProjection (SSet.yonedaEquiv.symm b)) := by
    dsimp only [k, g]
    rw [Category.assoc, Category.assoc, Category.assoc,
      leftUnstraighteningMap_projection, ← Category.assoc f, hf,
      hai, HomotopyLimits.pointCosliceUniverseIso_projection]
  have ke : IsPrecompositionEquivalence k :=
    (isPrecompositionEquivalence_of_iso
      (HomotopyLimits.pointCosliceUniverseIso.{u, u + 1} b)).comp
      ((isPrecompositionEquivalence_of_iso a.symm).comp
        (he.comp (isPrecompositionEquivalence_of_iso (asIso g))))
  exact covariantHomIsoOfCosliceEquivalence F b k kp ke

end SerrePositivity.InfinityCategories
