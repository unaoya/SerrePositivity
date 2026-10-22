module

public import SerrePositivity.InfinityCategories.F2.Ind.NativeFilteredPreservation
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.F2.CoconeValEquality

/-!
概要：小さい κ-filtered 余極限の保存性を通常の κ-filtered poset 上の余錐へ帰着する。
方針：元の余錐を同じ cofinal poset に制限し、像の全余錐の値の一致で戻す。
規約：正則 κ。元の余錐と関手を保持する。
使われ方：左 Kan 延長の一般の κ-filtered 余極限保存性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 通常の小さい κ-filtered poset 上の全 coherent 余錐を保存すれば一般にも保存する。 -/
lemma preservesSmallKappaFilteredColimits_of_poset {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    (h : ∀ (I : Type u) [PartialOrder I] [IsCardinalFiltered I κ]
      (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ X) (c : JoinCocone D),
      IsColimitCone c → IsColimitCone (mapJoinCocone F c)) :
    PreservesSmallKappaFilteredColimits κ F := by
  intro K hK hκ D c hc
  obtain ⟨I, o, f, hI, hN, hf⟩ := exists_cofinal_kappaFiltered_poset (κ := κ) K
  let := o
  have : IsCardinalFiltered I κ := hI
  let f' := (SSet.uliftFunctor.{u + 1, u}).map f
  have hf' := isRightCofinal_ulift f hf
  have hc' := (isColimitCone_iff_restrict_rightCofinal f' hf' c).mp hc
  have hi := h I (f' ≫ D) (c.restrict f') hc'
  apply (isColimitCone_iff_restrict_rightCofinal f' hf' (mapJoinCocone F c)).mpr
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _
    (Category.assoc _ _ _)).mp hi

end SerrePositivity.InfinityCategories.F2.Ind
