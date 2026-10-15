module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightNaturality
public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomConstantWeight

/-! # Source-frame functoriality in independent Hom and weight universes -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.SmallHomFrameWeights
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]

local instance : HasColimitsOfSize.{w, w} (ShrinkHoms C) := by
  have := SmallHomModel.locallyPresentable.{w} C
  exact Smith.locallyPresentable_hasColimits (C := ShrinkHoms C)

abbrev sourceFamily : (K ⥤ SimplexCategory ⥤ C) ⥤ K ⥤ SimplexCategory ⥤ ShrinkHoms C :=
  (Functor.whiskeringRight K (SimplexCategory ⥤ C) (SimplexCategory ⥤ ShrinkHoms C)).obj
    ((Functor.whiskeringRight SimplexCategory C (ShrinkHoms C)).obj
      (SmallHomModel.equivalence.{w} C).inverse)

abbrev family : (K ⥤ SimplexCategory ⥤ C) ⥤ (Kᵒᵖ ⥤ SSet.{w}) ⥤ C :=
  sourceFamily K ⋙ FrameWeightRealization.family K ⋙
    (Functor.whiskeringRight (Kᵒᵖ ⥤ SSet.{w}) (ShrinkHoms C) C).obj
      (SmallHomModel.equivalence.{w} C).functor

abbrev map {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) : functor K A ⟶ functor K B :=
  (family K).map a

end SerrePositivity.DiagramModel.SmallHomFrameWeights

namespace SerrePositivity.DiagramModel.SmallHomConstantWeight
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
local instance : HasColimitsOfSize.{w, w} (ShrinkHoms C) := by
  have := SmallHomModel.locallyPresentable.{w} C
  exact Smith.locallyPresentable_hasColimits (C := ShrinkHoms C)

abbrev degreeMap {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) (n : SimplexCategory) :
    ConstantWeightHom.degree K A n ⟶ ConstantWeightHom.degree K B n :=
  Functor.whiskerRight a ((evaluation SimplexCategory C).obj n)

omit [ModelCategory C] in
@[reassoc]
lemma degreeIso_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (n : SimplexCategory) :
    Functor.whiskerRight (ConstantWeightRealization.degreeMap K
        ((SmallHomFrameWeights.sourceFamily K).map a) n)
        (SmallHomModel.equivalence.{w} C).functor ≫ (degreeIso K B n).hom =
      (degreeIso K A n).hom ≫ degreeMap K a n := by
  apply NatTrans.ext
  funext k
  exact (SmallHomModel.equivalence.{w} C).counitIso.hom.naturality ((a.app k).app n)

set_option backward.isDefEq.respectTransparency false in
omit [ModelCategory C] in
@[reassoc]
lemma iso_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (n : SimplexCategory) :
    (SmallHomFrameWeights.map K a).app (ConstantWeightHom.weight K n) ≫ (iso K B n).hom =
      (iso K A n).hom ≫ colim.map (degreeMap K a n) := by
  let e := (SmallHomModel.equivalence.{w} C).functor
  have : e.IsLeftAdjoint := (SmallHomModel.equivalence.{w} C).toAdjunction.isLeftAdjoint
  let b := (SmallHomFrameWeights.sourceFamily K).map a
  have hb : (FrameWeightRealization.map K b).app (ConstantWeightHom.weight K n) ≫
      (ConstantWeightRealization.iso K (SmallHomFrameWeights.source K B) n).hom =
    (ConstantWeightRealization.iso K (SmallHomFrameWeights.source K A) n).hom ≫
      colim.map (ConstantWeightRealization.degreeMap K b n) :=
        ConstantWeightRealization.iso_frame_naturality K b n
  have hn := (preservesColimitNatIso (J := K) e).hom.naturality
    (ConstantWeightRealization.degreeMap K b n)
  change e.map (colim.map (ConstantWeightRealization.degreeMap K b n)) ≫
      (preservesColimitIso e (ConstantWeightHom.degree K (SmallHomFrameWeights.source K B) n)).hom =
    (preservesColimitIso e (ConstantWeightHom.degree K (SmallHomFrameWeights.source K A) n)).hom ≫
      colim.map (Functor.whiskerRight (ConstantWeightRealization.degreeMap K b n) e) at hn
  have hc := congrArg (fun z => (colim : (K ⥤ C) ⥤ C).map z)
    (degreeIso_frame_naturality K a n)
  change e.map ((FrameWeightRealization.map K b).app _) ≫
    (e.map (ConstantWeightRealization.iso K (SmallHomFrameWeights.source K B) n).hom ≫
      (preservesColimitIso e _).hom ≫ colim.map (degreeIso K B n).hom) =
    (e.map (ConstantWeightRealization.iso K (SmallHomFrameWeights.source K A) n).hom ≫
      (preservesColimitIso e _).hom ≫ colim.map (degreeIso K A n).hom) ≫ _
  rw [← Category.assoc, ← e.map_comp, hb, e.map_comp, Category.assoc]
  simp only [Category.assoc]
  apply congrArg (fun z => e.map
    (ConstantWeightRealization.iso K (SmallHomFrameWeights.source K A) n).hom ≫ z)
  rw [← Category.assoc, hn, Category.assoc, ← colim.map_comp, hc, colim.map_comp]

omit [ModelCategory C] in
@[reassoc]
lemma unitIso_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) :
    (SmallHomFrameWeights.map K a).app (ConstantWeightRealization.unitWeight K) ≫
        (unitIso K B).hom =
      (unitIso K A).hom ≫ colim.map
        (degreeMap K a (SimplexCategory.mk 0)) := by
  change (SmallHomFrameWeights.map K a).app (ConstantWeightRealization.unitWeight K) ≫
    ((SmallHomFrameWeights.functor K B).map _ ≫ _) =
      ((SmallHomFrameWeights.functor K A).map _ ≫ _) ≫ _
  rw [← Category.assoc, ← (SmallHomFrameWeights.map K a).naturality,
    Category.assoc, iso_frame_naturality, ← Category.assoc]

end SerrePositivity.DiagramModel.SmallHomConstantWeight
