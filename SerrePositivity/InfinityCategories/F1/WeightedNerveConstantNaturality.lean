module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveFunctor
public import SerrePositivity.InfinityCategories.F1.WeightedNerveFiber
public import SerrePositivity.InfinityCategories.F1.WeightedNerveBaseChange

/-!
概要：weighted nerve の係数値の定値包含の自然性。
方針：自然変換の後合成と、底の定値射列の後合成を各成分で計算する。
規約：係数の充填性は不要。
使われ方：Kerodon §5.3.3、係数の射の transport prism の端点の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：係数値の定値包含は係数の自然変換について自然。
方針：各初区間の Yoneda 単体への後合成を計算する。
規約：底の対象 c は固定する。
使われ方：Kerodon §5.3.3、係数の射を weighted nerve の射に移す端点の式。 -/
lemma weightedNerveConstantLift_map {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) (c : C) :
    weightedNerveConstantLift F c ≫ weightedNerveMap η =
      η.app c ≫ weightedNerveConstantLift G c := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  change (stdSimplex.map (simplexPrefixInclusion i.val d.unop.len _) ≫
      SSet.yonedaEquiv.symm x) ≫ η.app c =
    stdSimplex.map (simplexPrefixInclusion i.val d.unop.len _) ≫
      SSet.yonedaEquiv.symm ((η.app c).app d x)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]

/-- 概要：係数値の定値包含は底の関手による weighted nerve の比較と可換。
方針：定値射列に後合成した関手を、像の対象の定値関手と同定する。
規約：係数単体の初区間の図式は同じものを使う。
使われ方：Kerodon Remark 5.6.2.5、transport prism の底を元の圏に戻す端点の式。 -/
lemma weightedNerveConstantLift_baseMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) (d : D) :
    weightedNerveConstantLift (H ⋙ F) d ≫ weightedNerveBaseMap H F =
      weightedNerveConstantLift F (H.obj d) := by
  apply SSet.hom_ext
  intro k
  apply ConcreteCategory.hom_ext
  intro x
  have hσ : (CategoryTheory.Functor.const (Fin (k.unop.len + 1))).obj d ⋙ H =
      (CategoryTheory.Functor.const (Fin (k.unop.len + 1))).obj (H.obj d) := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp
  refine Sigma.ext hσ ?_
  have hex {G G' : Fin (k.unop.len + 1) ⥤ SSet.{u}} (h : G = G')
      (τ : simplexPrefixWeight k.unop.len ⟶ G) (τ' : simplexPrefixWeight k.unop.len ⟶ G')
      (he : ∀ i, HEq (τ.app i) (τ'.app i)) : HEq τ τ' := by
    subst G'
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    exact eq_of_heq (he i)
  apply hex (congrArg (fun Q ↦ Q ⋙ F) hσ)
  intro i
  rfl

end SerrePositivity.InfinityCategories
