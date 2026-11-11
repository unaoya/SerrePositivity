module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence

/-!
# 元の二つの単体的ホモトピーの直積

概要：同じ区間変数で二つの実際のホモトピーを直積にする。
方針：各次数の二成分を元のホモトピーで写す。
規約：始終域の Kan 性は要求しない。
使われ方：指定因子の有限直積の弱比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory
open scoped _root_.Simplicial

variable {A B C D : SSet.{u}} {f f' : A ⟶ B} {g g' : C ⟶ D}

def tensorHomotopyMap (H : SSet.Homotopy f f') (K : SSet.Homotopy g g') :
    (A ⊗ C) ⊗ Δ[1] ⟶ B ⊗ D where
  app n := ↾fun x => (H.h.app n (x.1.1, x.2), K.h.app n (x.1.2, x.2))
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (congrArg (fun k => k (x.1.1, x.2)) (H.h.naturality θ))
      (congrArg (fun k => k (x.1.2, x.2)) (K.h.naturality θ))

def tensorHomotopy (H : SSet.Homotopy f f') (K : SSet.Homotopy g g') :
    SSet.Homotopy (f ⊗ₘ g) (f' ⊗ₘ g') where
  h := tensorHomotopyMap H K
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (congrArg (fun k => k.app n x.1) H.h₀)
      (congrArg (fun k => k.app n x.2) K.h₀)
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (congrArg (fun k => k.app n x.1) H.h₁)
      (congrArg (fun k => k.app n x.2) K.h₁)

  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
