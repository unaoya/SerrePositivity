module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyTensorRight
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の図式を固定する円柱に全係数を加えても射影を保持する。
方針：係数射影と元の円柱の射影の二式を全次数で合成する。
規約：独立の全係数と実円柱を保持する。
使われ方：零面の pointed 比較を同じ底の相対関手空間に入れる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全係数を加えた元の実円柱も同じ図式を全時刻で固定する。 -/
lemma functorHomotopyTensorRight_postcomp_projection
    {X Z Y B : SSet.{u}} {f g : X ⟶ Z} (H : SSet.Homotopy f g)
    (A : SSet.{u}) (E : Z ⊗ A ⟶ Y) (p : Y ⟶ B) (q : Z ⟶ B) (b : X ⟶ B)
    (hE : E ≫ p = fst Z A ≫ q) (hH : H.h ≫ q = fst X Δ[1] ≫ b) :
    (functorHomotopyPostcomp (functorHomotopyTensorRight H A) E).h ≫ p =
      fst (X ⊗ A) Δ[1] ≫ (fst X A ≫ b) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, a⟩, t⟩
  change p.app d (E.app d (H.h.app d (x, t), a)) = b.app d x
  have he := congrArg (fun k : Z ⊗ A ⟶ B ↦ k.app d (H.h.app d (x, t), a)) hE
  have hh := congrArg (fun k : X ⊗ (Δ[1] : SSet.{u}) ⟶ B ↦ k.app d (x, t)) hH
  exact he.trans hh

end SerrePositivity.InfinityCategories.F2
