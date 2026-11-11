module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativeHomControl
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFamilyVertices

/-!
概要：全入力頂点で指定した全 native Hom を、同じ内ホーン全族の実二胞体に戻す。
方針：各頂点で長い Hom を置き換え、零骨格を指定した同じホーンの全族延長を取る。
規約：K の高次を含む二短辺は厳密に保持する。native Hom の指定は K の零単体で行う。
使われ方：Ind-S (9) の固定ホーン全族と各入力の全 native Hom の接続。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 二短辺の厳密一致は、同じ全内ホーンの厳密一致を与える。 -/
lemma triangle_horn_eq_of_faces {X : SSet.{u}} (f g : (Δ[2] : SSet.{u}) ⟶ X)
    (h₀ : stdSimplex.δ (0 : Fin 3) ≫ f = stdSimplex.δ (0 : Fin 3) ≫ g)
    (h₂ : stdSimplex.δ (2 : Fin 3) ≫ f = stdSimplex.δ (2 : Fin 3) ≫ g) :
    (horn 2 (1 : Fin 3)).ι ≫ f = (horn 2 (1 : Fin 3)).ι ≫ g := by
  apply horn.hom_ext'
  intro j hj
  rw [← Category.assoc, horn.ι_ι, ← Category.assoc, horn.ι_ι]
  fin_cases j
  · exact h₀
  · exact False.elim (hj rfl)
  · exact h₂

/-- 同じ全ホーン族を保ち、各入力で指定された全 native Hom を厳密に回収する。 -/
lemma triangleFamily_exists_with_native_homs
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [Quasicategory (SimplicialNerve C)] (K : SSet.{max u v})
    (F : (Δ[2] : SSet.{max u v}) ⊗ K ⟶ SimplicialNerve C)
    (m : ∀ k : K _⦋0⦌, nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶
      SimplicialCategory.sHom ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).obj ⟨ULift.up 0⟩)
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).obj ⟨ULift.up 2⟩))
    (hm : ∀ k : K _⦋0⦌,
      let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3)) (ULift.up 1) (ULift.up 2) ≫ m k =
        (t.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ ⊗ₘ t.map ⟨ULift.up 1⟩ ⟨ULift.up 2⟩) ≫
          eComp SSet (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 1⟩) (t.obj ⟨ULift.up 2⟩)) :
    ∃ F' : (Δ[2] : SSet.{max u v}) ⊗ K ⟶ SimplicialNerve C,
      ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F' = ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F ∧
      ∀ k : K _⦋0⦌,
        HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F' k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
          (m k) := by
  let t (k : K _⦋0⦌) := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)
  let s (k : K _⦋0⦌) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleWithNativeLongHom (t k) (m k) (hm k)
  obtain ⟨F', hF', hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerHornFamily_exists_with_vertex_fillers 2 1
    (by decide) (by decide) K F (fun k => SSet.yonedaEquiv.symm (s k)) (by
      intro k
      apply triangle_horn_eq_of_faces
      all_goals
        apply SSet.yonedaEquiv.injective
        rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
          Equiv.apply_symm_apply]
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleWithNativeLongHom_last _ _ _
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleWithNativeLongHom_first _ _ _)
  refine ⟨F', hF', ?_⟩
  intro k
  rw [hv, Equiv.apply_symm_apply]
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleWithNativeLongHom_native (t k) (m k) (hm k))

/-- 唯一の合成端の値だけを照合して、同じ全ホーン族と全 native Hom を回収する。 -/
lemma triangleFamily_exists_with_native_homs_of_full_value
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [Quasicategory (SimplicialNerve C)] (K : SSet.{max u v})
    (F : (Δ[2] : SSet.{max u v}) ⊗ K ⟶ SimplicialNerve C)
    (m : ∀ k : K _⦋0⦌, nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶
      SimplicialCategory.sHom ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).obj ⟨ULift.up 0⟩)
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).obj ⟨ULift.up 2⟩))
    (hm : ∀ k : K _⦋0⦌,
      (m k).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath) =
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app
          (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath)) :
    ∃ F' : (Δ[2] : SSet.{max u v}) ⊗ K ⟶ SimplicialNerve C,
      ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F' = ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F ∧
      ∀ k : K _⦋0⦌,
        HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F' k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
          (m k) := by
  apply triangleFamily_exists_with_native_homs K F m
  intro k
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLongHom_comp_of_full_value _ _ (hm k)]
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3)) (ULift.up 1) (ULift.up 2) ≫
      t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ =
      (t.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ ⊗ₘ t.map ⟨ULift.up 1⟩ ⟨ULift.up 2⟩) ≫
        eComp SSet (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 1⟩) (t.obj ⟨ULift.up 2⟩) :=
    t.map_comp ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ ⟨ULift.up 2⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathCompMap_eq_const, SSet.const_comp] at ht
  exact ht

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
