module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum

/-!
# 元の各因子の同型による依存和の同型

概要：同じ添字の元の各単体集合の同型から元の依存和の同型を得る。
方針：全次数で同じ添字を保持し、元の各成分の同型を適用する。
規約：単体作用素と元の標準射への整合を保持する。
使われ方：DK10.6(ii)の元の固定頂点列の因子と有限 Hom 積の和の比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum
open _root_.CategoryTheory

variable {I : Type u} {A B : I → SSet.{u}} (e : ∀ i, A i ≅ B i)

def mapIso : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.space A ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.space B :=
  NatIso.ofComponents (fun n => Equiv.toIso
    (Equiv.sigmaCongrRight (fun i => ((e i).app n).toEquiv))) (by
      intro n m θ
      apply ConcreteCategory.hom_ext
      intro x
      exact congrArg (Sigma.mk x.1)
        (ConcreteCategory.congr_hom ((e x.1).hom.naturality θ) x.2))

lemma mapIso_hom : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.mapIso e).hom = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.map (fun i => (e i).hom) := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum
