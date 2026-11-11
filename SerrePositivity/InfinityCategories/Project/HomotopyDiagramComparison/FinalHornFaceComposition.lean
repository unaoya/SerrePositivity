module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornPostcomposition

/-!
# 既知面からの Hom 回収と三対象の合成

概要：実際の最終外側ホーンの未知二区間の Hom を元の面データから構成する。
方針：native Path の合成と元の既知面の合成保存則を使う。
規約：全境界の可換性は証明し、Cartesian 性と実際の候補辺の同定は別に行う。
使われ方：HTT 5.2.4.6 の相対外側ホーン充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable {D : Type w} [EnrichedCategory SSet.{u} D]
variable {n : ℕ} {i : Fin (n + 3)}
  (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 豊穣関手の三つの対象を等号で移しても、元の合成保存則が成り立つ。 -/
lemma enrichedMap_comp_transport (F : EnrichedFunctor SSet D C) (x y z : D)
    (A B E : C) (hA : F.obj x = A) (hB : F.obj y = B) (hE : F.obj z = E) :
    eComp SSet x y z ≫ (F.map x z ≫ eqToHom (by rw [hA, hE])) =
      ((F.map x y ≫ eqToHom (by rw [hA, hB])) ⊗ₘ
        (F.map y z ≫ eqToHom (by rw [hB, hE]))) ≫
          SimplicialCategory.sHomComp A B E := by
  subst A
  subst B
  subst E
  simpa only [eqToHom_refl, Category.comp_id] using F.map_comp x y z

/-- 元の既知面を面の退縮で引き戻した、周囲の thickening 上の豊穣関手。 -/
def hornFaceRetractionFunctor (j : Fin (n + 3)) (hj : j ≠ i) :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n + 3)))) C :=
  (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).toOrderHom.uliftMap).comp SSet
    (σ.app _ (SSet.horn.face i j hj))

/-- 除外頂点と異なる対象では、引き戻した豊穣関手は元の共通対象を持つ。 -/
lemma hornFaceRetractionFunctor_obj (j : Fin (n + 3)) (hj : j ≠ i)
    (a : Fin (n + 3)) (ha : a ≠ j) :
    (hornFaceRetractionFunctor σ j hj).obj ⟨ULift.up a⟩ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a := by
  change (σ.app _ (SSet.horn.face i j hj)).obj
    ⟨ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).toOrderHom a)⟩ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.horn_face_obj, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_point j a ha]

/-- 引き戻した豊穣関手の Hom を共通対象へ移すと、元の既知面回収に一致する。 -/
lemma hornFaceRetractionFunctor_map (j : Fin (n + 3)) (hj : j ≠ i)
    (a b : Fin (n + 3)) (ha : a ≠ j) (hb : b ≠ j) :
    (hornFaceRetractionFunctor σ j hj).map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫ eqToHom (by
      rw [hornFaceRetractionFunctor_obj σ j hj a ha,
        hornFaceRetractionFunctor_obj σ j hj b hb]) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj a b ha hb := by
  simp only [hornFaceRetractionFunctor, EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell, Category.assoc, eqToHom_trans]
  rfl

/-- 同じ既知面から回収した Hom は、除外頂点を避ける三対象の合成を保存する。 -/
lemma hornHomViaFace_comp_general (j : Fin (n + 3)) (hj : j ≠ i)
    (a b c : Fin (n + 3)) (ha : a ≠ j) (hb : b ≠ j) (hc : c ≠ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{u} a) (ULift.up b) (ULift.up c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj a c ha hc =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj a b ha hb ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj b c hb hc) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) := by
  have h := enrichedMap_comp_transport (hornFaceRetractionFunctor σ j hj)
    ⟨ULift.up a⟩ ⟨ULift.up b⟩ ⟨ULift.up c⟩ _ _ _
    (hornFaceRetractionFunctor_obj σ j hj a ha)
    (hornFaceRetractionFunctor_obj σ j hj b hb)
    (hornFaceRetractionFunctor_obj σ j hj c hc)
  rw [hornFaceRetractionFunctor_map σ j hj a c ha hc,
    hornFaceRetractionFunctor_map σ j hj a b ha hb,
    hornFaceRetractionFunctor_map σ j hj b c hb hc] at h
  exact h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
