module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：実際のホモトピーに独立の全係数を加える。
方針：時刻と係数の二成分を並べ替え、係数を恒等で保持する。
規約：元の実円柱をそのまま使い、辺の代表を選び直さない。
使われ方：coslice 円柱を全 Hom 係数の pointed 族へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 実円柱に固定した全係数を直積として加えたホモトピー。 -/
def functorHomotopyTensorRight {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (A : SSet.{u}) : SSet.Homotopy (f ▷ A) (g ▷ A) where
  h := lift (lift (fst (X ⊗ A) Δ[1] ≫ fst X A) (snd (X ⊗ A) Δ[1]) ≫ H.h)
    (fst (X ⊗ A) Δ[1] ≫ snd X A)
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨x, a⟩
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app H.h₀ d) x
    · rfl
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨x, a⟩
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app H.h₁ d) x
    · rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.F2
