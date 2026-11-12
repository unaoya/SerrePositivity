module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import Mathlib.CategoryTheory.Widesubcategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCut

/-!
# 最初の非指定生成矢と前後の hammock の単体的依存和

概要：指定 prefix と残りの hammock を、元の非指定生成矢の始域・終域で束ねる。
方針：実際の二つの余極限の各次数の直積を元の生成矢で依存和にする。
規約：同じ Total 矢と指定部分圏の実際の W-hammock を使う。
使われ方：一段の切断を全単体作用素・全語に整合する射へ束ねる。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

abbrev Index := {g : Quiver.Total C // ¬ W g.hom}

def left (X : Paths C) (g : Quiver.Total C) : SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨g.left⟩

def right (Y : Paths C) (g : Quiver.Total C) : SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths g.right Y

def space (X Y : Paths C) : SSet.{max u v} where
  obj n := Σ g : Index W, (left W X g.val).obj n × (right W Y g.val).obj n
  map θ := ↾fun s => ⟨s.1, (left W X s.1.val).map θ s.2.1, (right W Y s.1.val).map θ s.2.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro s
    rcases s with ⟨g, p, r⟩
    change (⟨g, (left W X g.val).map (𝟙 n) p,
      (right W Y g.val).map (𝟙 n) r⟩ : Σ g : Index W,
        (left W X g.val).obj n × (right W Y g.val).obj n) = ⟨g, p, r⟩
    exact congrArg (fun q => (⟨g, q⟩ : Σ g : Index W,
      (left W X g.val).obj n × (right W Y g.val).obj n))
      (Prod.ext ((left W X g.val).map_id_apply n p) ((right W Y g.val).map_id_apply n r))
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro s
    rcases s with ⟨g, p, r⟩
    change (⟨g, (left W X g.val).map (θ ≫ φ) p,
      (right W Y g.val).map (θ ≫ φ) r⟩ : Σ g : Index W,
        (left W X g.val).obj _ × (right W Y g.val).obj _) =
      ⟨g, (left W X g.val).map φ ((left W X g.val).map θ p),
        (right W Y g.val).map φ ((right W Y g.val).map θ r)⟩
    exact congrArg (fun q => (⟨g, q⟩ : Σ g : Index W,
      (left W X g.val).obj _ × (right W Y g.val).obj _))
      (Prod.ext ((left W X g.val).map_comp_apply θ φ p)
        ((right W Y g.val).map_comp_apply θ φ r))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget
