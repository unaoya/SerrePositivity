module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 加法的 bar に使う厳密な単体的置換

## 概要
通常の小圏の図式から、射列の先頭の値の余積を各次数に持つ単体的対象を作る。

## 方針
添字作用素の先頭への射と、元の nerve の引き戻しで余積の各因子上の射を指定する。

## 規約
模型構造・有界性・加法性は不要。射列の添字は宇宙0で、値の圏の宇宙とは分ける。

## 使われ方
HTT 4.2.4.1、HA 1.2.4。strict 図式の bar の線形模型と単体的実現の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SerrePositivity.HomologicalAlgebra
variable {J : Type} [SmallCategory J]
variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

/-- 単体次数 n の射列に、その最初の対象の値を割り当てる。 -/
def replacementTerms (F : J ⥤ C) (n : SimplexCategoryᵒᵖ)
    (s : ComposableArrows J n.unop.len) : C := F.obj (s.obj 0)

/-- 余積の各因子上で指定した、単体作用素に対する同じ比較射。 -/
def replacementMap (F : J ⥤ C) {n m : SimplexCategoryᵒᵖ} (r : n ⟶ m) :
    (∐ replacementTerms F n) ⟶ ∐ replacementTerms F m :=
  Sigma.desc (fun s => F.map (s.map (homOfLE (Fin.zero_le (r.unop.toOrderHom 0)))) ≫
    Sigma.ι (replacementTerms F m) ((nerve J).map r s))

/-- 各元の因子上での単体作用素の公式。 -/
@[reassoc (attr := simp)]
theorem ι_replacementMap (F : J ⥤ C) {n m : SimplexCategoryᵒᵖ} (r : n ⟶ m)
    (s : ComposableArrows J n.unop.len) :
    Sigma.ι (replacementTerms F n) s ≫ replacementMap F r =
      F.map (s.map (homOfLE (Fin.zero_le (r.unop.toOrderHom 0)))) ≫
        Sigma.ι (replacementTerms F m) ((nerve J).map r s) := by
  exact Sigma.ι_comp_desc _ _

/-- 各単体次数で射列の先頭の値の余積を取る、厳密な単体的置換。 -/
def simplicialReplacement (F : J ⥤ C) : SimplicialObject C where
  obj n := ∐ replacementTerms F n
  map r := replacementMap F r
  map_id n := by
    apply Sigma.hom_ext
    intro s
    simp [replacementMap, CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  map_comp {n m k} r t := by
    apply Sigma.hom_ext
    intro s
    rw [ι_replacementMap, ι_replacementMap_assoc, ι_replacementMap,
      ← Category.assoc, ← F.map_comp]
    congr 1
    · congr 1
      change s.map _ = s.map _ ≫ s.map _
      rw [← s.map_comp]
      rfl

/-- 元の自然変換を、各余積因子で同じ成分を持つ単体的置換の射へ送る。 -/
def simplicialReplacementMap {F G : J ⥤ C} (η : F ⟶ G) :
    simplicialReplacement F ⟶ simplicialReplacement G where
  app n := Sigma.desc (fun s => η.app (s.obj 0) ≫ Sigma.ι (replacementTerms G n) s)
  naturality {n m} r := by
    apply Sigma.hom_ext
    intro s
    change Sigma.ι (replacementTerms F n) s ≫ (replacementMap F r ≫ _) =
      Sigma.ι (replacementTerms F n) s ≫ (_ ≫ replacementMap G r)
    rw [ι_replacementMap_assoc]
    simp only [Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      ι_replacementMap]
    exact η.naturality_assoc _ _

/-- 単体的置換の射も元の各因子の射と厳密に一致する。 -/
@[reassoc (attr := simp)]
theorem ι_simplicialReplacementMap {F G : J ⥤ C} (η : F ⟶ G)
    (n : SimplexCategoryᵒᵖ) (s : ComposableArrows J n.unop.len) :
    Sigma.ι (replacementTerms F n) s ≫ (simplicialReplacementMap η).app n =
      η.app (s.obj 0) ≫ Sigma.ι (replacementTerms G n) s := Sigma.ι_comp_desc _ _

/-- 厳密な図式圏の全自然変換を保持する、単体的置換の関手。 -/
def simplicialReplacementFunctor : (J ⥤ C) ⥤ SimplicialObject C where
  obj := simplicialReplacement
  map := simplicialReplacementMap
  map_id F := by
    apply NatTrans.ext
    funext n
    apply Sigma.hom_ext
    intro s
    simp
    exact (Category.comp_id _).symm
  map_comp η θ := by
    apply NatTrans.ext
    funext n
    apply Sigma.hom_ext
    intro s
    simp [Category.assoc]

end SerrePositivity.HomologicalAlgebra
