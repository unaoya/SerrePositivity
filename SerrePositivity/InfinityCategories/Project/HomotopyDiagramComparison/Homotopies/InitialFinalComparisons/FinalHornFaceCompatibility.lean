module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FaceCompatibilityEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FullFaceCompatibility

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

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 二つの切断点の合成面上の回収は、同じ交わりで厳密に一致する。 -/
lemma finalHornCompositionHom_composition_overlap (a b c d : Fin (n + 3))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hpab : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b)
    (hpbc : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval b c)
    (hpcd : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval c d)
    (hpac : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a c)
    (hpbd : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval b d) :
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} a) (c := ULift.up d) (ULift.up b) ⊓
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) from inf_le_left) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom σ a b d hab (hbc.trans hcd) hpab hpbd =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} a) (c := ULift.up d) (ULift.up b) ⊓
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) from inf_le_right) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom σ a c d (hab.trans hbc) hcd hpac hpcd := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathTripleToIntersection_epi
    (ULift.up.{u} a) (ULift.up b) (ULift.up c) (ULift.up d) hbc
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathTripleToIntersection
    (ULift.up.{u} a) (ULift.up b) (ULift.up c) (ULift.up d))).mp
  simp only [← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathTripleToIntersection_toFirst, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathTripleToIntersection_toSecond]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_on_product, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_on_product]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, y⟩, z⟩
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ d
  let f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a b hab hpab
  let g := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ b c hbc hpbc
  let h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ c d hcd hpcd
  have hbd := congrArg (fun k ↦ k.app m (y, z))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_comp σ b c d hbc hcd hpbc hpcd hpbd)
  have hac := congrArg (fun k ↦ k.app m (x, y))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_comp σ a b c hab hbc hpab hpbc hpac)
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ b d (hbc.trans hcd) hpbd).app m
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up b) (ULift.up c) (ULift.up d)).app m (y, z)) =
      (SimplicialCategory.sHomComp B D E).app m (g.app m y, h.app m z) at hbd
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a c (hab.trans hbc) hpac).app m
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up a) (ULift.up b) (ULift.up c)).app m (x, y)) =
      (SimplicialCategory.sHomComp A B D).app m (f.app m x, g.app m y) at hac
  change (SimplicialCategory.sHomComp A B E).app m (f.app m x,
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ b d (hbc.trans hcd) hpbd).app m
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up b) (ULift.up c) (ULift.up d)).app m (y, z))) =
    (SimplicialCategory.sHomComp A D E).app m
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a c (hab.trans hbc) hpac).app m
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up a) (ULift.up b) (ULift.up c)).app m (x, y)), h.app m z)
  rw [hbd, hac]
  exact congrArg (fun k ↦ k.app m ((f.app m x, g.app m y), h.app m z))
    (e_assoc' SSet A B D E)

/-- 同じ既知面内の零座標面と合成面の回収は、交わりで厳密に一致。 -/
lemma finalHornCompositionHom_zero_overlap (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2))
    (a b c : Fin (n + 2)) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval (j.succAbove a) (j.succAbove b))
    (hpbc : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval (j.succAbove b) (j.succAbove c)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (j.succAbove a)) (b := ULift.up (j.succAbove c))
      (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b))).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj (j.succAbove a) (j.succAbove c)
        (Fin.succAbove_ne j a) (Fin.succAbove_ne j c) =
    SSet.Subcomplex.homOfLE
      (show (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (j.succAbove a))
        (b := ULift.up (j.succAbove c)) (ULift.up j) ⊓
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b))) ≤
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b)) from inf_le_right) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom σ (j.succAbove a) (j.succAbove b) (j.succAbove c)
        ((Fin.strictMono_succAbove j).monotone hab)
        ((Fin.strictMono_succAbove j).monotone hbc) hpab hpbc := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixedFaceIso.{u} j a b c).hom).mp
  simp only [← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixedFaceIso_hom_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixedFaceIso_hom_toThrough]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_on_product]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceCompositionMap_eq_native, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_on_face]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_on_face σ j hj a b hab hpab,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_on_face σ j hj b c hbc hpbc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell_comp σ (SSet.horn.face (Fin.last (n + 2)) j hj) a b c

/-- 任意の共通端点と切断点で、零座標面と合成面の元の回収は一致する。 -/
lemma finalHornCompositionHom_zero_overlap_general (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2))
    (a b c : Fin (n + 3)) (haj : a ≠ j) (hbj : b ≠ j) (hcj : c ≠ j)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b)
    (hpbc : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval b c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} a) (b := ULift.up c) (ULift.up j) ⊓
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj a c haj hcj =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} a) (b := ULift.up c) (ULift.up j) ⊓
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) from inf_le_right) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom σ a b c hab hbc hpab hpbc := by
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq haj
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hbj
  obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hcj
  exact finalHornCompositionHom_zero_overlap σ j hj a b c
    ((Fin.strictMono_succAbove j).le_iff_le.mp hab)
    ((Fin.strictMono_succAbove j).le_iff_le.mp hbc) hpab hpbc

/-- 全区間の二つの既知合成面は、元の交わりで厳密に一致する。 -/
lemma finalHornUpperCompositionHom_overlap (b c : Fin (n + 3))
    (hb0 : 0 < b) (hbn : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (hc0 : 0 < c) (hcn : c < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
        (c := ULift.up (Fin.last (n + 2))) (ULift.up b) ⊓
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) from inf_le_left) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbn =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
        (c := ULift.up (Fin.last (n + 2))) (ULift.up b) ⊓
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) from inf_le_right) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ c hc0 hcn := by
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
    (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (Fin.last (n + 2))) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j) from inf_le_left) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom σ j (ne_of_lt hjn) hj0 hjn =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (Fin.last (n + 2))) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) from inf_le_right) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbp := by
  by_cases hbj : b = j
  · subst b
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixed_self_hom_ext _ _ _ _ _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
  exact finalHornCompositionHom_zero_overlap_general σ j (ne_of_lt hjn)
    0 b (Fin.last (n + 2)) (ne_of_lt hj0) hbj (ne_of_gt hjn)
    (Fin.zero_le b) (Fin.le_last b) (Or.inr hbp) (Or.inl (ne_of_gt hb0))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
