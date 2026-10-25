module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarAugmentation

/-!
概要：添字関手に沿う通常のホモロジー bar の比較。
方針：係数を保ち、各単体ラベルを添字関手との合成へ送る。
規約：元の coherent G の strict 化には使わない。
使われ方：終頂点を持つ下方部分圏から filtered な全体への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] {J K : Type u} [Category.{u} J] [Category.{u} K]
  (F : J ⥤ ModuleCat.{u} R) (H : K ⥤ J)

def dgHomologyBarIndexMapComponent (Δ : SimplexCategoryᵒᵖ) :
    (dgHomologyBarSimplicial R (H ⋙ F)).obj Δ ⟶ (dgHomologyBarSimplicial R F).obj Δ :=
  Sigma.desc (fun s => Sigma.ι (dgHomologyBarFamily R F Δ) (s ⋙ H))

@[reassoc (attr := simp)]
lemma dgHomologyBarIndexMapComponent_ι (Δ : SimplexCategoryᵒᵖ) (s : (nerve K).obj Δ) :
    Sigma.ι (dgHomologyBarFamily R (H ⋙ F) Δ) s ≫
      dgHomologyBarIndexMapComponent R F H Δ =
        Sigma.ι (dgHomologyBarFamily R F Δ) (s ⋙ H) := by
  simp only [dgHomologyBarIndexMapComponent, Sigma.ι_comp_desc]

def dgHomologyBarIndexMap : dgHomologyBarSimplicial R (H ⋙ F) ⟶
    dgHomologyBarSimplicial R F where
  app Δ := dgHomologyBarIndexMapComponent R F H Δ
  naturality Δ Γ α := by
    apply Sigma.hom_ext
    intro s
    simp only [dgHomologyBarSimplicial, Category.assoc,
      dgHomologyBarIndexMapComponent_ι_assoc, dgHomologyBarMap_ι_assoc,
      dgHomologyBarIndexMapComponent_ι, dgHomologyBarMap_ι]
    rfl

@[reassoc (attr := simp)]
lemma dgHomologyBarIndexMap_ι (Δ : SimplexCategoryᵒᵖ) (s : (nerve K).obj Δ) :
    Sigma.ι (dgHomologyBarFamily R (H ⋙ F) Δ) s ≫
      (dgHomologyBarIndexMap R F H).app Δ =
        Sigma.ι (dgHomologyBarFamily R F Δ) (s ⋙ H) := by
  exact dgHomologyBarIndexMapComponent_ι R F H Δ s

end SerrePositivity.InfinityCategories
