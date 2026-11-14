module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveIso

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber

/-!
概要：Grothendieckのweighted nerve比較が元の指定頂点を厳密に保つ。
方針：次数零のprefixは元の同じfiber対象に戻り、そのYoneda表示を比較する。
規約：IS-W2 R03eの指定点付きの型。弱同値や成分への置換は行わない。
使われ方：元の指定点を持つ同じ底上の比較の入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 同じ比較の前向き写像は、元の指定fiber対象の頂点を厳密に保つ。 -/
theorem grothWeightedNerveForward_vertex (i : I) (x : F.obj i) :
    (grothWeightedNerveForward F).app (Opposite.op ⦋0⦌)
      (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
        (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
          (Opposite.op ⦋0⦌) (nerveVertex x) := by
  refine Sigma.ext (show (nerveVertex (⟨i,x⟩ : Grothendieck F)) ⋙
    Grothendieck.forget F = (CategoryTheory.Functor.const (Fin 1)).obj i from rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext k
  have hk : k = (0 : Fin 1) := Fin.eq_zero k
  subst k
  change (SSet.yonedaEquiv (X := nerve (F.obj i)) (n := SimplexCategory.mk 0)).symm
    (grothWeightedPrefixFiber F (nerveVertex (⟨i,x⟩ : Grothendieck F)) 0) =
      stdSimplex.map (simplexPrefixInclusion 0 0 (by omega)) ≫
        (SSet.yonedaEquiv (X := nerve (F.obj i)) (n := SimplexCategory.mk 0)).symm (nerveVertex x)
  have hi : simplexPrefixInclusion 0 0 (by omega) = 𝟙 (SimplexCategory.mk 0) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext a
    exact Fin.ext rfl
  rw [hi, CategoryTheory.Functor.map_id, Category.id_comp]
  apply congrArg (SSet.yonedaEquiv (X := nerve (F.obj i)) (n := SimplexCategory.mk 0)).symm
  refine CategoryTheory.Functor.ext (fun k => ?_) ?_
  · have hk : k = Fin.last 0 := Fin.eq_zero k
    subst k
    exact grothWeightedPrefixFiber_last F (nerveVertex (⟨i,x⟩ : Grothendieck F)) 0
  · intro k l f
    have hk : k = Fin.last 0 := Fin.eq_zero k
    have hl : l = Fin.last 0 := Fin.eq_zero l
    subst k
    subst l
    have hf : f = 𝟙 (Fin.last 0) := Subsingleton.elim _ _
    subst f
    change (grothWeightedPrefixFiber F (nerveVertex (⟨i,x⟩ : Grothendieck F)) 0).map
      (𝟙 (Fin.last 0)) = eqToHom _ ≫ (nerveVertex x).map (𝟙 (Fin.last 0)) ≫ eqToHom _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      eqToHom_trans, eqToHom_refl]

/-- R03e：Grothendieckのnerveとprefix重み付きnerveの、射影と指定点を保つ厳密な同型。 -/
theorem exists_grothendieckWeightedNerveIso :
    ∃ e : nerve (Grothendieck F) ≅ weightedNerve (F ⋙ nerveFunctor),
      e.hom ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
        nerveMap (Grothendieck.forget F) ∧
      ∀ (i : I) (x : F.obj i),
        e.hom.app (Opposite.op ⦋0⦌) (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
          (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
            (Opposite.op ⦋0⦌) (nerveVertex x) := by
  refine ⟨grothendieckWeightedNerveIso F, grothendieckWeightedNerveIso_projection F, ?_⟩
  intro i x
  simpa only [grothendieckWeightedNerveIso, asIso_hom] using grothWeightedNerveForward_vertex F i x

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
