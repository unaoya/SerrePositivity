module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyDiagram
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
概要：通常のホモロジー図式の simplicial bar を構成する。
方針：各単体の始点係数を直和し、単調写像の最初の辺で係数を運ぶ。
規約：これはホモロジーを取った後の図式であり、元の coherent G の代替ではない。
使われ方：実 bar の単体次元フィルトレーションの一次ホモロジー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [Category.{u} J]
  (F : J ⥤ ModuleCat.{u} R)

def dgHomologyBarFamily (Δ : SimplexCategoryᵒᵖ) (s : (nerve J).obj Δ) : ModuleCat R :=
  F.obj (s.obj 0)

def dgHomologyBarMap {Δ Γ : SimplexCategoryᵒᵖ} (α : Δ ⟶ Γ) :
    (∐ dgHomologyBarFamily R F Δ) ⟶ ∐ dgHomologyBarFamily R F Γ :=
  Sigma.desc (fun s =>
    F.map (s.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0)))) ≫
      Sigma.ι (dgHomologyBarFamily R F Γ) ((nerve J).map α s))

@[reassoc (attr := simp)]
lemma dgHomologyBarMap_ι {Δ Γ : SimplexCategoryᵒᵖ} (α : Δ ⟶ Γ)
    (s : (nerve J).obj Δ) :
    Sigma.ι (dgHomologyBarFamily R F Δ) s ≫ dgHomologyBarMap R F α =
      F.map (s.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0)))) ≫
        Sigma.ι (dgHomologyBarFamily R F Γ) ((nerve J).map α s) := by
  simp only [dgHomologyBarMap, Sigma.ι_comp_desc]

lemma dgHomologyBarMap_id (Δ : SimplexCategoryᵒᵖ) :
    dgHomologyBarMap R F (𝟙 Δ) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  simp only [dgHomologyBarMap_ι, Category.comp_id]
  change F.map (s.map (𝟙 (0 : Fin (Δ.unop.len + 1)))) ≫
    Sigma.ι (dgHomologyBarFamily R F Δ) s = _
  rw [s.map_id, F.map_id, Category.id_comp]

lemma dgHomologyBarMap_comp {Δ Γ Λ : SimplexCategoryᵒᵖ}
    (α : Δ ⟶ Γ) (β : Γ ⟶ Λ) :
    dgHomologyBarMap R F (α ≫ β) = dgHomologyBarMap R F α ≫ dgHomologyBarMap R F β := by
  apply Sigma.hom_ext
  intro s
  rw [dgHomologyBarMap_ι, ← Category.assoc, dgHomologyBarMap_ι,
    Category.assoc, dgHomologyBarMap_ι, ← Category.assoc, ← F.map_comp]
  erw [← s.map_comp]
  rfl

def dgHomologyBarSimplicial : SimplicialObject (ModuleCat R) where
  obj Δ := ∐ dgHomologyBarFamily R F Δ
  map α := dgHomologyBarMap R F α
  map_id := dgHomologyBarMap_id R F
  map_comp := dgHomologyBarMap_comp R F

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
