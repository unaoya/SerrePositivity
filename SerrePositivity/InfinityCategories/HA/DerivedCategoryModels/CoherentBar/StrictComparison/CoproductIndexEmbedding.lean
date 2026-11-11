module
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：添字の単射が誘導する加群の直和包含は次数ごとに単射である。
方針：像の添字だけを選ぶ射影を作り、直和包含との合成を恒等にする。
規約：無限和を使わず、選択は各包含先の一つの添字に限る。
使われ方：bar の下方部分圏の次数包含と、フィルトレーションの段階商。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits
variable (R : Type u) [CommRing R] {ι κ : Type u} (p : ι → κ)
  (V : κ → ModuleCat.{u} R)

def dgBarCoproductIndexInclusion : (∐ fun i => V (p i)) ⟶ ∐ V :=
  Sigma.desc (fun i => Sigma.ι V (p i))

def dgBarCoproductIndexProjection : (∐ V) ⟶ ∐ fun i => V (p i) := by
  classical
  exact Sigma.desc (fun k => if h : ∃ i, p i = k then
    eqToHom (congrArg V h.choose_spec.symm) ≫ Sigma.ι (fun i => V (p i)) h.choose else 0)

lemma dgBarCoproductIndexProjection_ι (hp : Function.Injective p) (i : ι) :
    Sigma.ι V (p i) ≫ dgBarCoproductIndexProjection R p V =
      Sigma.ι (fun j => V (p j)) i := by
  classical
  have h : ∃ j, p j = p i := ⟨i, rfl⟩
  have hc : h.choose = i := hp h.choose_spec
  simp only [dgBarCoproductIndexProjection, Sigma.ι_comp_desc, dif_pos h]
  exact Sigma.eqToHom_comp_ι (fun j => V (p j)) hc

@[reassoc]
lemma dgBarCoproductIndexInclusion_projection (hp : Function.Injective p) :
    dgBarCoproductIndexInclusion R p V ≫ dgBarCoproductIndexProjection R p V = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  simp only [dgBarCoproductIndexInclusion, Sigma.ι_comp_desc_assoc,
    dgBarCoproductIndexProjection_ι R p V hp, Category.comp_id]

lemma dgBarCoproductIndexInclusion_injective (hp : Function.Injective p) :
    Function.Injective (dgBarCoproductIndexInclusion R p V) := by
  intro a b hab
  have h := congrArg (fun z => dgBarCoproductIndexProjection R p V z) hab
  simpa only [← ModuleCat.comp_apply, dgBarCoproductIndexInclusion_projection R p V hp,
    ModuleCat.id_apply] using h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
