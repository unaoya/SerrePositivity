module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.UnderMap
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ConeLeg
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes

/-!
概要：Under の nerve の coslice 比較と通常の標準錐を同定する。
方針：join の両端と混合辺で比較し nerve への射の外延性を使う。
規約：同じ宇宙の小さい圏の任意の指定対象を扱う。
使われ方：B5 の指定余単位の右 Kan 局所錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：Under の忘却関手上の標準錐は元の始点を頂点に持つ。
方針：両境界と頂点から各対象への一次単体を照合する。
規約：元の指定対象と Under の構造射を保持する。
使われ方：B5 の右 Kan の標準錐の古典比較。 -/
def underForgetCone : Cone (Under.forget c) where
  pt := c
  π :=
    { app := fun x ↦ x.hom
      naturality := fun x y f ↦ by
        change 𝟙 c ≫ y.hom = x.hom ≫ f.right
        rw [Category.id_comp]
        exact (Under.w f).symm }

/-- 概要：Under の nerve の uncurry の脚は元の構造射を表す。
方針：両境界と頂点から各対象への一次単体を照合する。
規約：元の指定対象と Under の構造射を保持する。
使われ方：B5 の右 Kan の標準錐の古典比較。 -/
lemma nerveUnderUncurry_leg (i : Under c) :
    (sliceUnderUncurry (SerrePositivity.InfinityCategories.F1B.nerveUnderMap c)).app (Opposite.op ⦋1⦌) (SerrePositivity.InfinityCategories.F1B.coneLegSimplex i) =
      ComposableArrows.mk₁ i.hom := by
  change sliceUnderUncurryApp (SerrePositivity.InfinityCategories.F1B.nerveUnderMap c) 1
    (Join.mkOfSum rfl (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) (nerveVertex i)) = _
  rw [sliceUnderUncurryApp_mkOfSum]
  change ((SSet.yonedaEquiv (X := nerve C)).symm (SerrePositivity.InfinityCategories.F1B.nerveUnderChain c (nerveVertex i))).app
    (Opposite.op ⦋1⦌)
    ((pointJoinStdSimplexIso 0).hom.app (Opposite.op ⦋1⦌)
      (Join.mkOfSum rfl (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))
        (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)))) = _
  rw [SerrePositivity.InfinityCategories.F1B.pointJoinStdSimplexIso_zero_leg]
  change SerrePositivity.InfinityCategories.F1B.nerveUnderChain c (nerveVertex i) = _
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 概要：Under の nerve の uncurry は通常の標準錐の nerve に一致する。
方針：両境界と頂点から各対象への一次単体を照合する。
規約：元の指定対象と Under の構造射を保持する。
使われ方：B5 の右 Kan の標準錐の古典比較。 -/
lemma nerveUnderMap_uncurry : sliceUnderUncurry (SerrePositivity.InfinityCategories.F1B.nerveUnderMap c) =
    (SerrePositivity.InfinityCategories.F1B.nerveCone (underForgetCone c)).val := by
  have h₀ : joinInl (Δ[0] : SSet.{u}) (nerve (Under c)) ≫
      (SerrePositivity.InfinityCategories.F1B.nerveCone (underForgetCone c)).val = nervePoint c := by
    change joinInl (Δ[0] : SSet.{u}) (nerve (Under c)) ≫
      (HomotopyLimits.initialJoinNerveMap (Under c) ≫
        nerveMap (SerrePositivity.InfinityCategories.F1B.coneWithInitialFunctor (underForgetCone c))) = _
    rw [← Category.assoc, HomotopyLimits.joinInl_initialJoinNerveMap]
    rfl
  have h₁ : joinInr (Δ[0] : SSet.{u}) (nerve (Under c)) ≫
      sliceUnderUncurry (SerrePositivity.InfinityCategories.F1B.nerveUnderMap c) =
        joinInr (Δ[0] : SSet.{u}) (nerve (Under c)) ≫
          (SerrePositivity.InfinityCategories.F1B.nerveCone (underForgetCone c)).val := by
    rw [sliceUnderUncurry_projection, (SerrePositivity.InfinityCategories.F1B.nerveCone (underForgetCone c)).property,
      SerrePositivity.InfinityCategories.F1B.nerveUnderMap_projection]
  apply SerrePositivity.InfinityCategories.F1B.nerve_joinPoint_hom_ext
  · exact (sliceUnderUncurry_fixed (SerrePositivity.InfinityCategories.F1B.nerveUnderMap c)).trans h₀.symm
  · exact h₁
  · intro i
    rw [nerveUnderUncurry_leg, SerrePositivity.InfinityCategories.F1B.nerveCone_leg]
    rfl

end SerrePositivity.InfinityCategories.F1B
