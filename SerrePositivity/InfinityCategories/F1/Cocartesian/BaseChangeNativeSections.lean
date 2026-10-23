module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeAssociativity
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityEvaluation

/-!
概要：既存の section 結合比較は、元の全空間の結合同型との実際の後合成。
方針：引き戻しの両射影で、全パラメーターの section の評価を照合する。
規約：既存の分類側の比較成分をそのまま保持する。
使われ方：元の全相対 Hom の共役作用と分類側の結合比較を結び付ける。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  {E : SSet.{u}} (p : E ⟶ nerve C) [CocartesianFibration p] (l : A ⥤ D) (k : D ⥤ C)

/-- 既存の section の結合比較の展開は、全空間の同じ結合同型との実際の後合成。 -/
lemma cocartesianBaseChangeAssociativityComponent_native_uncurry (a : A) {T : SSet.{u}}
    (s : T ⟶ kanCocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) a) :
    relativeFunctorUncurry ((s ≫ (cocartesianBaseChangeAssociativityComponent p l k a).hom) ≫
      kanCocartesianSectionsι (pullback.fst (nerveMap (l ⋙ k)) p)
        (nerveMap (Under.forget a))) =
    relativeFunctorUncurry (s ≫ kanCocartesianSectionsι
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) (nerveMap (Under.forget a))) ≫
        (cocartesianBaseChangeNativeAssociativity p l k).hom := by
  let x := relativeFunctorUncurry
    ((s ≫ (cocartesianBaseChangeAssociativityComponent p l k a).hom) ≫
      kanCocartesianSectionsι (pullback.fst (nerveMap (l ⋙ k)) p)
        (nerveMap (Under.forget a)))
  let y := relativeFunctorUncurry (s ≫ kanCocartesianSectionsι
    (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) (nerveMap (Under.forget a)))
  let e := cocartesianBaseChangeNativeAssociativity p l k
  change x = y ≫ e.hom
  apply pullback.hom_ext
  · have hx := relativeFunctorUncurry_projection
      ((s ≫ (cocartesianBaseChangeAssociativityComponent p l k a).hom) ≫
        kanCocartesianSectionsι (pullback.fst (nerveMap (l ⋙ k)) p)
          (nerveMap (Under.forget a)))
    have hy := relativeFunctorUncurry_projection (s ≫ kanCocartesianSectionsι
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) (nerveMap (Under.forget a)))
    exact hx.trans (hy.symm.trans ((Category.assoc y e.hom _).trans
      (congrArg (fun f ↦ y ≫ f)
        (cocartesianBaseChangeNativeAssociativity_hom_fst p l k))).symm)
  · exact (cocartesianBaseChangeAssociativityComponent_uncurry_snd p l k a s).trans
      ((Category.assoc y e.hom _).trans (congrArg (fun f ↦ y ≫ f)
        (cocartesianBaseChangeNativeAssociativity_hom_snd p l k))).symm

end SerrePositivity.InfinityCategories
