module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeAssociativity
public import SerrePositivity.InfinityCategories.F1.OverPullbackColimits

/-!
概要：二重引き戻しの同型と射影の合成は、元の底上の射による直接の誘導射。
方針：元の引き戻しの両射影と結合同型の射影公式を使う。
規約：同じ底上の射と元の全空間を保持する。
使われ方：元の局所 Hom の底変換作用と Segal 制限の厳密な照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 二つのセルと同じその合成を結ぶ、元の底上の射。 -/
def cocartesianBaseChangeOverMap :
    Over.mk (nerveMap (l ⋙ k)) ⟶ Over.mk (nerveMap k) :=
  Over.homMk (nerveMap l) rfl

/-- 逆結合同型に二重引き戻しの射影を続けると、直接の引き戻しの元の誘導射になる。 -/
lemma cocartesianBaseChangeNativeAssociativity_inv_projection
    {E : SSet.{u}} (p : E ⟶ nerve C) [CocartesianFibration p] :
    (cocartesianBaseChangeNativeAssociativity p l k).inv ≫
      pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p) =
    (overPullbackUnderlying p).map (cocartesianBaseChangeOverMap l k) := by
  let e := cocartesianBaseChangeNativeAssociativity p l k
  have hf : e.inv ≫ pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p) =
      pullback.fst (nerveMap (l ⋙ k)) p := by
    rw [Iso.inv_comp_eq]
    exact (cocartesianBaseChangeNativeAssociativity_hom_fst p l k).symm
  apply pullback.hom_ext
  · calc
      (e.inv ≫ pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p)) ≫
          pullback.fst (nerveMap k) p =
        e.inv ≫ pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p) ≫ nerveMap l :=
          (Category.assoc _ _ _).trans (congrArg (fun f ↦ e.inv ≫ f)
            (pullback.condition (f := nerveMap l) (g := pullback.fst (nerveMap k) p)).symm)
      _ = pullback.fst (nerveMap (l ⋙ k)) p ≫ nerveMap l := by
        rw [← Category.assoc, hf]
      _ = (overPullbackUnderlying p).map (cocartesianBaseChangeOverMap l k) ≫
          pullback.fst (nerveMap k) p :=
        (overPullbackUnderlying_map_fst p (cocartesianBaseChangeOverMap l k)).symm
  · exact (Category.assoc _ _ _).trans
      ((cocartesianBaseChangeNativeAssociativity_inv_snd p l k).trans
        (overPullbackUnderlying_map_snd p (cocartesianBaseChangeOverMap l k)).symm)

end SerrePositivity.InfinityCategories
