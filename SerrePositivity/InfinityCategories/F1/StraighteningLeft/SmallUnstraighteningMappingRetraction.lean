module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.UnstraighteningFamilyComparison

/-!
概要：小さい底上の unstraightening の写像空間比較は関手同型まで右逆を持つ。
方針：相対写像空間全体の普遍的な射の族を一度に復元する。
規約：左逆や比較射全体の同値性はこの定理に含めない。
使われ方：写像空間比較の存在側を全パラメーターに組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい相対射の族は比較射の像として関手同型まで復元できる。
方針：collage による復元と普遍的な持ち上げの比較を合成する。
規約：底とパラメーターが各次数で小さい場合。
使われ方：比較射への普遍的な右逆の構成。 -/
lemma exists_small_unstraighteningFamily_preimage {B K : SSet.{u + 1}}
    [∀ n, Small.{u} (B.obj n)] [∀ n, Small.{u} (K.obj n)]
    (F G : B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G =
      CartesianMonoidalCategory.fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) :
    ∃ t : K ⟶ leftUnstraighteningTransformationSpace F G,
      Nonempty (FunctorIso (t ≫ leftUnstraighteningMappingSpaceMap F G)
        (relativeFunctorCurry f hf)) := by
  obtain ⟨t, W, hw₀, hw₁, hwp⟩ := exists_small_coherentFamily_recovery F G f hf
  exact ⟨t, ⟨unstraighteningFamilyComparisonIso F G t f hf W hw₀ hw₁ hwp⟩⟩

/-- 概要：小さい底上の写像空間比較には空間全体で関手同型となる右逆が存在する。
方針：小さい相対写像空間そのものをパラメーターとし普遍的な射の族を復元する。
規約：各頂点での選択を別々に行わない。左逆は別途証明する。
使われ方：Kerodon Corollary 5.6.0.6 の写像空間比較の全体での復元。 -/
lemma small_leftUnstraighteningMappingSpaceMap_exists_rightInverse
    {B : SSet.{u + 1}} [∀ n, Small.{u} (B.obj n)] (F G : B ⟶ SpaceInfinity.{u}) :
    ∃ t : relativeFunctorSpace (leftUnstraighteningProjection G)
        (leftUnstraighteningProjection F) ⟶ leftUnstraighteningTransformationSpace F G,
      Nonempty (FunctorIso (t ≫ leftUnstraighteningMappingSpaceMap F G) (𝟙 _)) := by
  let Y := relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
  let f := relativeFunctorUncurry (𝟙 Y)
  have hf := relativeFunctorUncurry_projection (𝟙 Y)
  obtain ⟨t, ⟨e⟩⟩ := exists_small_unstraighteningFamily_preimage F G f hf
  have hc : relativeFunctorCurry f hf = 𝟙 Y := by
    apply relativeFunctorUncurry_injective (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F)
    exact relativeFunctorUncurry_curry f hf
  rw [hc] at e
  exact ⟨t, ⟨e⟩⟩

end SerrePositivity.InfinityCategories
