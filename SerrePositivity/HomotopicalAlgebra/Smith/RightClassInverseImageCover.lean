module

public import SerrePositivity.HomotopicalAlgebra.Smith.PresentableOverIteration
public import SerrePositivity.HomotopicalAlgebra.Smith.LiftingColimitRefinement

/-! # Local presentable covers for inverse images of generated right classes

The bounded successor construction is allowed to depend on its target. Each
image transition factors through the right class; the shorter regular
iteration therefore has its image in that class.
-/

@[expose] public section
universe w v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace SerrePositivity.Smith

lemma rightClass_inverseImage_localCover
    {C : Type u₁} [Category.{v₁} C] [HasColimitsOfSize.{w, w} C]
    {E : Type u₂} [Category.{v₂} E] [HasColimitsOfSize.{w, w} E]
    (I : MorphismProperty E) (μ ν : Cardinal.{w}) [Fact μ.IsRegular] [Fact ν.IsRegular]
    [OrderBot μ.ord.ToType] (hμν : μ < ν) [IsCardinalAccessibleCategory C ν]
    (F : C ⥤ Arrow E) [F.IsCardinalAccessible μ] [F.IsCardinalAccessible ν]
    [F.PreservesCardinalPresentable ν]
    [∀ i : I.toSet, IsCardinalPresentable i.val.left μ]
    [∀ i : I.toSet, IsCardinalPresentable i.val.right μ]
    (r : PresentableWeakReflection (arrowProperty I.rlp) ν) :
    LocalPresentableCover ((arrowProperty I.rlp).inverseImage F) ν where
  cover {X} hX A _ f := by
    let J := μ.ord.ToType
    have : NoMaxOrder J := Cardinal.noMaxOrder
      (Cardinal.IsRegular.aleph0_le (Fact.out : μ.IsRegular))
    have hJ : HasCardinalLT J ν := by
      simpa only [J, hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_toType,
        Cardinal.card_ord] using hμν
    have hJA := (hasCardinalLT_arrow_iff_of_isThin J ν
      (Cardinal.IsRegular.aleph0_le (Fact.out : ν.IsRegular))).2 hJ
    let Bnd := PresentableOverIteration.category ν X
    have : HasIterationOfShape J Bnd := PresentableOverIteration.hasIterationOfShape ν X J hJ
    let G : Bnd ⥤ C := (PresentableOverIteration.property ν X).ι ⋙ Over.forget X
    have hstep (b : Bnd) : ∃ (b' : Bnd) (i : b ⟶ b')
        (u : r.R.obj (F.obj (G.obj b)) ⟶ F.obj (G.obj b')),
        r.unit.app (F.obj (G.obj b)) ≫ u = F.map (G.map i) := by
      have : IsCardinalPresentable b.obj.left ν := b.property
      obtain ⟨B, hB, i, p, u, hip, hu⟩ :=
        exists_weakReflection_transition F r hX b.obj.left b.obj.hom
      let b' : Bnd := ⟨Over.mk p, hB⟩
      exact ⟨b', ObjectProperty.homMk (Over.homMk i hip), u, hu⟩
    choose next toNext u hu using hstep
    let Φ : SuccStruct Bnd :=
      { X₀ := ⟨Over.mk f, inferInstanceAs (IsCardinalPresentable A ν)⟩
        succ := next
        toSucc := toNext }
    have : PreservesColimitsOfShape J (PresentableOverIteration.property ν X).ι :=
      PresentableOverIteration.inclusion_preservesColimitsOfShape ν X J hJA
    have := F.preservesColimitsOfShape_of_isCardinalAccessible μ J
    have hc := isColimitOfPreserves (G ⋙ F) (Φ.isColimitIterationCocone J)
    have htrans : ∀ j, ∃ (k : J) (a : j ⟶ k) (p : Arrow E) (_ : I.rlp p.hom)
        (α : ((Φ.iterationFunctor J) ⋙ G ⋙ F).obj j ⟶ p)
        (β : p ⟶ ((Φ.iterationFunctor J) ⋙ G ⋙ F).obj k),
        α ≫ β = ((Φ.iterationFunctor J) ⋙ G ⋙ F).map a := by
      intro j
      let Y := (Φ.iterationFunctor J).obj j
      let e := Φ.iterationFunctorObjSuccIso j (not_isMax j)
      refine ⟨Order.succ j, homOfLE (Order.le_succ j), r.R.obj (F.obj (G.obj Y)),
        r.obj_mem _, r.unit.app _, u Y ≫ F.map (G.map e.inv), ?_⟩
      have h := hu Y
      change r.unit.app (F.obj (G.obj Y)) ≫ u Y = F.map (G.map (Φ.toSucc Y)) at h
      change r.unit.app (F.obj (G.obj Y)) ≫ (u Y ≫ F.map (G.map e.inv)) =
        F.map (G.map ((Φ.iterationFunctor J).map (homOfLE (Order.le_succ j))))
      rw [Φ.iterationFunctor_map_succ j (not_isMax j), G.map_comp, F.map_comp,
        ← Category.assoc, h]
    have hp := LiftingColimitRefinement.rlp_of_factorizing_transitions I μ hc htrans
    let B := Φ.iteration J
    refine ⟨B.obj.left, B.property, hp, (Φ.ιIteration J).hom.left, B.obj.hom, ?_⟩
    exact Over.w (Φ.ιIteration J).hom

end SerrePositivity.Smith
