module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Products.Basic

/-!
# 元の全単体による nerve の二項積同型

概要：二つの nerve の単体的積を、元の積圏の nerve と明示的に同型にする。
方針：二つの射列を成分ごとの積関手にし、逆は二つの射影を使う。
規約：全単体・全作用素の元のデータを保持する。
使われ方：固定語の zigzag の連結関手から graph の単体的合成を構成する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.NerveProduct
open CategoryTheory MonoidalCategory

variable (C D : Type u) [Category.{v} C] [Category.{v} D]

/-- 二つの元の射列を積関手として組にする。 -/
def pair : nerve C ⊗ nerve D ⟶ nerve (C × D) where
  app _ := ↾fun p => p.1.prod' p.2
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- 元の積圏の射列の二つの射影。 -/
def unpair : nerve (C × D) ⟶ nerve C ⊗ nerve D where
  app _ := ↾fun σ => (σ ⋙ CategoryTheory.Prod.fst C D, σ ⋙ CategoryTheory.Prod.snd C D)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro σ
    rfl

/-- 元の射列の積と射影による、全作用素での同型。 -/
def iso : nerve C ⊗ nerve D ≅ nerve (C × D) where
  hom := pair C D
  inv := unpair C D
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl

lemma pair_natural {C' D' : Type u} [Category.{v} C'] [Category.{v} D']
    (F : C ⥤ C') (G : D ⥤ D') :
    (nerveMap F ⊗ₘ nerveMap G) ≫ pair C' D' = pair C D ≫ nerveMap (F.prod G) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.NerveProduct
