module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornComposition
public import SerrePositivity.InfinityCategories.Coherent.CompositionCompatibility
public import SerrePositivity.InfinityCategories.Coherent.FaceCompatibilityEndpoints
public import SerrePositivity.InfinityCategories.Coherent.FullFaceCompatibility

/-!
概要：最終外側ホーンの零座標面と既知合成面の交わりで、元の Hom 写像は一致する。
方針：元の面制限・三対象の合成・結合則と面の交わりの同型で証明する。
規約：整合性を追加仮定にしない。使われ方：実際の外側ホーンからの空洞写像の貼合せ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 二つの切断点の合成面上の回収は、同じ交わりで厳密に一致する。 -/
lemma finalHornCompositionHom_composition_overlap (a b c d : Fin (n + 3))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hpab : FinalHornKnownInterval a b)
    (hpbc : FinalHornKnownInterval b c)
    (hpcd : FinalHornKnownInterval c d)
    (hpac : FinalHornKnownInterval a c)
    (hpbd : FinalHornKnownInterval b d) :
    SSet.Subcomplex.homOfLE
      (show pathThrough (a := ULift.up.{u} a) (c := ULift.up d) (ULift.up b) ⊓
        pathThrough (ULift.up c) ≤ pathThrough (ULift.up b) from inf_le_left) ≫
      finalHornCompositionHom σ a b d hab (hbc.trans hcd) hpab hpbd =
    SSet.Subcomplex.homOfLE
      (show pathThrough (a := ULift.up.{u} a) (c := ULift.up d) (ULift.up b) ⊓
        pathThrough (ULift.up c) ≤ pathThrough (ULift.up c) from inf_le_right) ≫
      finalHornCompositionHom σ a c d (hab.trans hbc) hcd hpac hpcd := by
  have := pathTripleToIntersection_epi
    (ULift.up.{u} a) (ULift.up b) (ULift.up c) (ULift.up d) hbc
  apply (cancel_epi (pathTripleToIntersection
    (ULift.up.{u} a) (ULift.up b) (ULift.up c) (ULift.up d))).mp
  simp only [← Category.assoc]
  rw [pathTripleToIntersection_toFirst, pathTripleToIntersection_toSecond]
  simp only [Category.assoc]
  rw [finalHornCompositionHom_on_product, finalHornCompositionHom_on_product]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, y⟩, z⟩
  let A := hornObj σ a
  let B := hornObj σ b
  let D := hornObj σ c
  let E := hornObj σ d
  let f := finalHornKnownIntervalHom σ a b hab hpab
  let g := finalHornKnownIntervalHom σ b c hbc hpbc
  let h := finalHornKnownIntervalHom σ c d hcd hpcd
  have hbd := congrArg (fun k ↦ k.app m (y, z))
    (finalHornKnownIntervalHom_comp σ b c d hbc hcd hpbc hpcd hpbd)
  have hac := congrArg (fun k ↦ k.app m (x, y))
    (finalHornKnownIntervalHom_comp σ a b c hab hbc hpab hpbc hpac)
  change (finalHornKnownIntervalHom σ b d (hbc.trans hcd) hpbd).app m
    ((pathCompMap (ULift.up b) (ULift.up c) (ULift.up d)).app m (y, z)) =
      (SimplicialCategory.sHomComp B D E).app m (g.app m y, h.app m z) at hbd
  change (finalHornKnownIntervalHom σ a c (hab.trans hbc) hpac).app m
    ((pathCompMap (ULift.up a) (ULift.up b) (ULift.up c)).app m (x, y)) =
      (SimplicialCategory.sHomComp A B D).app m (f.app m x, g.app m y) at hac
  change (SimplicialCategory.sHomComp A B E).app m (f.app m x,
    (finalHornKnownIntervalHom σ b d (hbc.trans hcd) hpbd).app m
      ((pathCompMap (ULift.up b) (ULift.up c) (ULift.up d)).app m (y, z))) =
    (SimplicialCategory.sHomComp A D E).app m
      ((finalHornKnownIntervalHom σ a c (hab.trans hbc) hpac).app m
        ((pathCompMap (ULift.up a) (ULift.up b) (ULift.up c)).app m (x, y)), h.app m z)
  rw [hbd, hac]
  exact congrArg (fun k ↦ k.app m ((f.app m x, g.app m y), h.app m z))
    (e_assoc' SSet A B D E)

/-- 同じ既知面内の零座標面と合成面の回収は、交わりで厳密に一致。 -/
lemma finalHornCompositionHom_zero_overlap (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2))
    (a b c : Fin (n + 2)) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : FinalHornKnownInterval (j.succAbove a) (j.succAbove b))
    (hpbc : FinalHornKnownInterval (j.succAbove b) (j.succAbove c)) :
    (pathAvoids (a := ULift.up.{u} (j.succAbove a)) (b := ULift.up (j.succAbove c))
      (ULift.up j) ⊓ pathThrough (ULift.up (j.succAbove b))).ι ≫
      hornHomViaFace σ j hj (j.succAbove a) (j.succAbove c)
        (Fin.succAbove_ne j a) (Fin.succAbove_ne j c) =
    SSet.Subcomplex.homOfLE
      (show (pathAvoids (a := ULift.up.{u} (j.succAbove a))
        (b := ULift.up (j.succAbove c)) (ULift.up j) ⊓
          pathThrough (ULift.up (j.succAbove b))) ≤
            pathThrough (ULift.up (j.succAbove b)) from inf_le_right) ≫
      finalHornCompositionHom σ (j.succAbove a) (j.succAbove b) (j.succAbove c)
        ((Fin.strictMono_succAbove j).monotone hab)
        ((Fin.strictMono_succAbove j).monotone hbc) hpab hpbc := by
  apply (cancel_epi (pathMixedFaceIso.{u} j a b c).hom).mp
  simp only [← Category.assoc]
  rw [pathMixedFaceIso_hom_ι, pathMixedFaceIso_hom_toThrough]
  rw [Category.assoc, finalHornCompositionHom_on_product]
  rw [pathFaceCompositionMap_eq_native, Category.assoc, pathFaceMap, hornHomViaFace_on_face]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [pathFaceMap]
  rw [finalHornKnownIntervalHom_on_face σ j hj a b hab hpab,
    finalHornKnownIntervalHom_on_face σ j hj b c hbc hpbc]
  exact hornHomOnCell_comp σ (SSet.horn.face (Fin.last (n + 2)) j hj) a b c

/-- 任意の共通端点と切断点で、零座標面と合成面の元の回収は一致する。 -/
lemma finalHornCompositionHom_zero_overlap_general (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2))
    (a b c : Fin (n + 3)) (haj : a ≠ j) (hbj : b ≠ j) (hcj : c ≠ j)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : FinalHornKnownInterval a b)
    (hpbc : FinalHornKnownInterval b c) :
    (pathAvoids (a := ULift.up.{u} a) (b := ULift.up c) (ULift.up j) ⊓
      pathThrough (ULift.up b)).ι ≫ hornHomViaFace σ j hj a c haj hcj =
    SSet.Subcomplex.homOfLE
      (show pathAvoids (a := ULift.up.{u} a) (b := ULift.up c) (ULift.up j) ⊓
        pathThrough (ULift.up b) ≤ pathThrough (ULift.up b) from inf_le_right) ≫
      finalHornCompositionHom σ a b c hab hbc hpab hpbc := by
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq haj
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hbj
  obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hcj
  exact finalHornCompositionHom_zero_overlap σ j hj a b c
    ((Fin.strictMono_succAbove j).le_iff_le.mp hab)
    ((Fin.strictMono_succAbove j).le_iff_le.mp hbc) hpab hpbc

/-- 全区間の二つの既知合成面は、元の交わりで厳密に一致する。 -/
lemma finalHornUpperCompositionHom_overlap (b c : Fin (n + 3))
    (hb0 : 0 < b) (hbn : b < finalHornPenultimate n)
    (hc0 : 0 < c) (hcn : c < finalHornPenultimate n) :
    SSet.Subcomplex.homOfLE
      (show pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
        (c := ULift.up (Fin.last (n + 2))) (ULift.up b) ⊓
          pathThrough (ULift.up c) ≤ pathThrough (ULift.up b) from inf_le_left) ≫
      finalHornUpperCompositionHom σ b hb0 hbn =
    SSet.Subcomplex.homOfLE
      (show pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
        (c := ULift.up (Fin.last (n + 2))) (ULift.up b) ⊓
          pathThrough (ULift.up c) ≤ pathThrough (ULift.up c) from inf_le_right) ≫
      finalHornUpperCompositionHom σ c hc0 hcn := by
  rcases le_total b c with hbc | hcb
  · exact finalHornCompositionHom_composition_overlap σ 0 b c (Fin.last (n + 2))
      (Fin.zero_le b) hbc (Fin.le_last c)
      (Or.inr hbn) (Or.inl (ne_of_gt hb0)) (Or.inl (ne_of_gt hc0))
      (Or.inr hcn) (Or.inl (ne_of_gt hb0))
  · have he := finalHornCompositionHom_composition_overlap σ 0 c b
      (Fin.last (n + 2)) (Fin.zero_le c) hcb (Fin.le_last b)
      (Or.inr hcn) (Or.inl (ne_of_gt hc0)) (Or.inl (ne_of_gt hb0))
      (Or.inr hbn) (Or.inl (ne_of_gt hc0))
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact (congrArg (fun k ↦ k.app m ⟨F.1, ⟨F.2.2, F.2.1⟩⟩) he).symm

/-- 全区間の任意の零座標面と既知合成面は、元の交わりで厳密に一致。 -/
lemma finalHornZeroHom_composition_overlap (j b : Fin (n + 3))
    (hj0 : 0 < j) (hjn : j < Fin.last (n + 2))
    (hb0 : 0 < b) (hbp : b < finalHornPenultimate n) :
    SSet.Subcomplex.homOfLE
      (show pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (Fin.last (n + 2))) (ULift.up j) ⊓ pathThrough (ULift.up b) ≤
          pathAvoids (ULift.up j) from inf_le_left) ≫
        hornInnerZeroHom σ j (ne_of_lt hjn) hj0 hjn =
    SSet.Subcomplex.homOfLE
      (show pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (Fin.last (n + 2))) (ULift.up j) ⊓ pathThrough (ULift.up b) ≤
          pathThrough (ULift.up b) from inf_le_right) ≫
      finalHornUpperCompositionHom σ b hb0 hbp := by
  by_cases hbj : b = j
  · subst b
    exact pathMixed_self_hom_ext _ _ _ _ _
  simp only [hornInnerZeroHom, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
  exact finalHornCompositionHom_zero_overlap_general σ j (ne_of_lt hjn)
    0 b (Fin.last (n + 2)) (ne_of_lt hj0) hbj (ne_of_gt hjn)
    (Fin.zero_le b) (Fin.le_last b) (Or.inr hbp) (Or.inl (ne_of_gt hb0))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
