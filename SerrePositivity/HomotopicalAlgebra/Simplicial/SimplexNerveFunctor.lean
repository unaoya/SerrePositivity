module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation
public import SerrePositivity.CategoryTheory.LabelledChain
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# 単体圏nerveの各次数を次数ごとのラベルによる直和として表す同型を構成する

## 概要
単体圏nerveの各次数を次数ごとのラベルによる直和として表す同型を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0565][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0565
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The simplex-nerve functor and its exact degreewise label decomposition

A chain of elements is determined by its original chain of simplex
operators and its first label. The decomposition is natural in the whole
simplicial set and uses no model structure.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SimplexNerve

abbrev functor : SSet.{v} ⥤ SSet.{v} := Functor.elementsFunctor ⋙ nerveFunctor

def augmentation : functor.{v} ⟶ 𝟭 SSet.{v} where
  app X := SimplexNerveAugmentation.augmentation X
  naturality {_ _} f := SimplexNerveAugmentation.naturality _ f

abbrev Chains (n : SimplexCategoryᵒᵖ) := ComposableArrows SimplexCategoryᵒᵖ n.unop.len

def chainEquiv (X : SSet.{v}) (n : SimplexCategoryᵒᵖ) :
    ((functor.obj X).obj n) ≃ Σ δ : Chains n, X.obj (δ.obj 0) where
  toFun c := ⟨c ⋙ Functor.Elements.π X, (c.obj 0).val⟩
  invFun s := LabelledChain.lift X s.1 s.2
  left_inv c := LabelledChain.reconstruct X c
  right_inv s := by
    rcases s with ⟨δ, x⟩
    refine Sigma.ext (CategoryTheory.Functor.ext (fun _ => rfl)) ?_
    apply heq_of_eq
    change X.map (δ.map (𝟙 0)) x = x
    rw [δ.map_id, X.map_id]
    rfl

def degreeLabels (n : SimplexCategoryᵒᵖ) : SSet.{v} ⥤ Type v where
  obj X := Σ δ : Chains n, X.obj (δ.obj 0)
  map f := ↾fun s => ⟨s.1, f.app (s.1.obj 0) s.2⟩

def degreeIso (n : SimplexCategoryᵒᵖ) :
    functor.{v} ⋙ (evaluation SimplexCategoryᵒᵖ (Type v)).obj n ≅ degreeLabels n :=
  NatIso.ofComponents (fun X => (chainEquiv X n).toIso) (by intro _ _ _; rfl)

def degreeFamily (n : SimplexCategoryᵒᵖ) : SSet.{v} ⥤ Discrete (Chains n) ⥤ Type v where
  obj X := Discrete.functor (fun δ => X.obj (δ.obj 0))
  map f := Discrete.natTrans (fun δ => f.app (δ.as.obj 0))

instance degreeFamilyPreserves (n : SimplexCategoryᵒᵖ) :
    PreservesColimitsOfSize.{v, v} (degreeFamily.{v} n) := by
  apply preservesColimits_of_evaluation
  intro δ
  change PreservesColimitsOfSize.{v, v}
    ((evaluation SimplexCategoryᵒᵖ (Type v)).obj (δ.as.obj 0))
  infer_instance

abbrev degreeSum (n : SimplexCategoryᵒᵖ) : SSet.{v} ⥤ Type v := degreeFamily n ⋙ colim

/-- 単体圏nerveの各次数を次数ごとのラベルによる直和として表す同型を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。
-/
def degreeSumIso (n : SimplexCategoryᵒᵖ) : degreeSum.{v} n ≅ degreeLabels n :=
  NatIso.ofComponents (fun X => Types.coproductIso (fun δ : Chains n => X.obj (δ.obj 0))) (by
    intro X Y f
    apply Sigma.hom_ext
    intro δ
    simp only [degreeSum, degreeFamily, Functor.comp_obj, colim_obj, Functor.comp_map,
      colim_map, ι_colimMap_assoc, Discrete.functor_obj_eq_as]
    change (f.app (δ.obj 0) ≫ Sigma.ι (fun δ : Chains n => Y.obj (δ.obj 0)) δ) ≫
      (Types.coproductIso (fun δ : Chains n => Y.obj (δ.obj 0))).hom =
        Sigma.ι (fun δ : Chains n => X.obj (δ.obj 0)) δ ≫
          (Types.coproductIso (fun δ : Chains n => X.obj (δ.obj 0))).hom ≫
            (degreeLabels n).map f
    rw [Category.assoc, Types.coproductIso_ι_comp_hom]
    rw [← Category.assoc, Types.coproductIso_ι_comp_hom]
    rfl)

instance preservesColimits : PreservesColimitsOfSize.{v, v} functor.{v} := by
  apply preservesColimits_of_evaluation
  intro n
  have : PreservesColimitsOfSize.{v, v} (degreeSum.{v} n) := inferInstance
  exact (preservesColimitsOfSize_iff_of_natIso
    ((degreeIso n) ≪≫ (degreeSumIso n).symm)).mpr this

end SerrePositivity.SimplicialModel.SimplexNerve
