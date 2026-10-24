module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OverLeg
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.CoconeNaturality

/-!
概要：Over の nerve の slice 比較と通常の標準余錐を同定する。
方針：両境界と構造射の脚を照合して高次の射の一致を得る。
規約：同じ宇宙の小さい圏の元の指定終点を保持する。
使われ方：B5 の指定単位の左 Kan 局所余錐の比較。
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

/-- 概要：Over の忘却関手上の標準余錐は元の終点を頂点に持つ。
方針：join の両境界と全ての混合辺を照合する。
規約：元の指定対象と Over の構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の古典比較。 -/
def overForgetCocone : Cocone (Over.forget c) where
  pt := c
  ι :=
    { app := fun x ↦ x.hom
      naturality := fun x y f ↦ by
        change f.left ≫ y.hom = x.hom ≫ 𝟙 c
        rw [Category.comp_id]
        exact Over.w f }

/-- 概要：Over の nerve の uncurry は通常の標準余錐の nerve と一致する。
方針：join の両境界と全ての混合辺を照合する。
規約：元の指定対象と Over の構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の古典比較。 -/
lemma nerveOverIso_uncurry : sliceOverUncurry (SerrePositivity.InfinityCategories.F1B.nerveOverIso c).hom =
    (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv (overForgetCocone c)).val := by
  apply SerrePositivity.InfinityCategories.F1B.nerve_joinTerminal_hom_ext
  · rw [sliceOverUncurry_projection, (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv (overForgetCocone c)).property,
      SerrePositivity.InfinityCategories.F1B.nerveOverIso_projection]
  · rw [sliceOverUncurry_fixed, SerrePositivity.InfinityCategories.F1B.nerveCocone_point]
    rfl
  · intro x
    change ((SerrePositivity.InfinityCategories.F1B.nerveOverIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x)).val.app
      (Opposite.op ⦋1⦌) (SerrePositivity.InfinityCategories.F1B.joinCoconeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) = _
    rw [SerrePositivity.InfinityCategories.F1B.nerveOverIso_leg, SerrePositivity.InfinityCategories.F1B.nerveCocone_leg]
    rfl

end SerrePositivity.InfinityCategories.F1B
