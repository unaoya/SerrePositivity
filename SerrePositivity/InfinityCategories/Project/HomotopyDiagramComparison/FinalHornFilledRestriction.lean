module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornFilledFunctor

/-!
# 復元した最終ホーン単体の全既知面への制限

概要：最終外側ホーンの二つの未知 Hom を、元の豊穣単体と相対充填へ組み立てる。
方針：全三対象の合成、全既知面への制限、薄い底の一意性を順に照合する。
規約：元の cf 置換と底射影を使い、内ホーンの欠損頂点条件を仮定しない。
使われ方：HTT 5.2.4.6 の元の右 Quillen 候補辺の Cartesian 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)
  (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up (Fin.last (n + 2)))) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))
  (f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)))

/-- 充填用 Hom は、全ての既知面の零座標面上で元の Hom 回収と一致する。 -/
lemma finalHornFillHom_on_zero
    (hf : ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom σ j)
    (hz : ∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom σ j (ne_of_lt hjn) hj0 hjn)
    (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2))
    (a b : Fin (n + 3)) (haj : a ≠ j) (hbj : b ≠ j) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} a) (b := ULift.up b) (ULift.up j)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f a b =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} a) (b := ULift.up b) (ULift.up j)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj a b haj hbj := by
  by_cases hab : a ≤ b
  swap
  · apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact (hab (F.1.obj 0).le).elim
  by_cases hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b
  · rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_known σ g f a b hab hp]
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq haj
    obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hbj
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso.{u} j a b).hom).mp
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso_hom_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap]
    exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_on_face σ j hj a b
      ((Fin.strictMono_succAbove j).le_iff_le.mp hab) hp).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_on_face σ j hj a b).symm
  obtain ⟨rfl, hb | hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUnknownInterval_endpoints a b hp
  · subst b
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_front]
    have hj0 : 0 < j := lt_of_le_of_ne (Fin.zero_le j) haj
    have hjn : j < Fin.last (n + 2) := lt_of_le_of_ne (Fin.le_last j) hj
    have hjp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.lt_finalHornPenultimate_of_lt_last_ne j hjn (Ne.symm hbj)
    exact hf (.inl ⟨ULift.up.{u} j, hj0, hjp⟩)
  · subst b
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_full]
    have hj0 : 0 < j := lt_of_le_of_ne (Fin.zero_le j) haj
    have hjn : j < Fin.last (n + 2) := lt_of_le_of_ne (Fin.le_last j) (Ne.symm hbj)
    exact hz j hj0 hjn

/-- 全ての頂点対の充填用 Hom を既知面へ制限すると、元の同じ面の Hom に一致する。 -/
lemma finalHornFillHom_on_face
    (hf : ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom σ j)
    (hz : ∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom σ j (ne_of_lt hjn) hj0 hjn)
    (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) (a b : Fin (n + 2)) :
    (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
      ⟨ULift.up.{u} a⟩ ⟨ULift.up b⟩ ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f (j.succAbove a) (j.succAbove b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ (SSet.horn.face (Fin.last (n + 2)) j hj) a b := by
  have h := finalHornFillHom_on_zero σ g f hf hz j hj (j.succAbove a) (j.succAbove b)
    (Fin.succAbove_ne j a) (Fin.succAbove_ne j b)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j a b ≫ _ = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso_hom_ι, Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso_hom_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_on_face σ j hj a b

/-- 復元した豊穣単体の各既知面は、元のホーンの同じ単体に一致する。 -/
lemma finalHornFilledFunctor_face
    (hf : ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom σ j)
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow σ) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g)
    (hz : ∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom σ j (ne_of_lt hjn) hj0 hjn)
    (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
    (SimplicialNerve C).δ j (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFilledFunctor σ g f hf hg hfg) =
      σ.app _ (SSet.horn.face (Fin.last (n + 2)) j hj) := by
  apply EnrichedFunctor.ext SSet (fun X ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.horn_face_obj σ j hj X.as.down).symm)
  intro X Y
  change ((SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
    ⟨ULift.up.{u} X.as.down⟩ ⟨ULift.up Y.as.down⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f (j.succAbove X.as.down) (j.succAbove Y.as.down)) ≫ _ = _
  rw [finalHornFillHom_on_face σ g f hf hz j hj]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell_transport_back σ (SSet.horn.face (Fin.last (n + 2)) j hj)
    X.as.down Y.as.down

/-- 元の全頂点上に復元した豊穣単体から、標準単体を始域とする充填写像を作る。 -/
def finalHornFiller
    (hf : ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom σ j)
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow σ) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g) : (Δ[n + 2] : SSet.{max u v}) ⟶ SimplicialNerve C :=
  yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFilledFunctor σ g f hf hg hfg)

/-- 充填写像の最終外側ホーンへの制限は元のホーン写像に一致する。 -/
lemma finalHornFiller_restriction
    (hf : ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom σ j)
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow σ) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g)
    (hz : ∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom σ j (ne_of_lt hjn) hj0 hjn) :
    (Λ[n + 2, Fin.last (n + 2)]).ι ≫ finalHornFiller σ g f hf hg hfg = σ := by
  apply SSet.horn.hom_ext
  intro j hj
  rw [← finalHornFilledFunctor_face σ g f hf hg hfg hz j hj, NatTrans.comp_app]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
