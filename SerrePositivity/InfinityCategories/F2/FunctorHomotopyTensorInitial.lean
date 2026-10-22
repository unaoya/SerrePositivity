module

public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyTensorProjection

/-!
概要：同じ部分図式を固定する円柱に独立の全係数を加えても固定条件を保つ。
方針：元の部分図式の固定式と全係数作用の同じ値を各次数で合成する。
規約：元の実円柱を保持する。
使われ方：零面の全 pointed 円柱の始点固定条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全係数を加えても元の円柱の部分図式の固定条件を保持する。 -/
lemma functorHomotopyTensorRight_postcomp_initial
    {D X Z Y : SSet.{u}} {f g : X ⟶ Z} (H : SSet.Homotopy f g)
    (A : SSet.{u}) (E : Z ⊗ A ⟶ Y) (j : D ⟶ X) (w : D ⟶ Z) (v : D ⊗ A ⟶ Y)
    (hH : (j ▷ Δ[1]) ≫ H.h = fst D Δ[1] ≫ w) (hE : (w ▷ A) ≫ E = v) :
    ((j ▷ A) ▷ Δ[1]) ≫
      (functorHomotopyPostcomp (functorHomotopyTensorRight H A) E).h =
        fst (D ⊗ A) Δ[1] ≫ v := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, a⟩, t⟩
  change E.app d (H.h.app d (j.app d x, t), a) = v.app d (x, a)
  have hh := congrArg (fun k : D ⊗ (Δ[1] : SSet.{u}) ⟶ Z ↦ k.app d (x, t)) hH
  have he := congrArg (fun k : D ⊗ A ⟶ Y ↦ k.app d (x, a)) hE
  exact (congrArg (fun z ↦ E.app d (z, a)) hh).trans he

end SerrePositivity.InfinityCategories.F2
