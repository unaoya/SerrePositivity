module
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：係数の同型を伴う添字分解を、反復直和の余積性へ移す。
方針：sigma 型による直和の平坦化、係数同型、添字同値の三つの同型を合成する。
規約：実加群の余積の普遍性を使い、全射や分解を追加公理にしない。
使われ方：ホモロジー bar の非退化単体による splitting。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits
variable (R : Type u) [CommRing R] {A : Type} {B : A → Type u} {S : Type u}
  (V : S → ModuleCat.{u} R) (W : ∀ a, B a → ModuleCat.{u} R)
  (e : (Σ a, B a) ≃ S) (w : ∀ a b, W a b ≅ V (e ⟨a, b⟩))

def dgBarCoproductDecompositionIso : (∐ fun a => ∐ W a) ≅ ∐ V :=
  sigmaSigmaIso B W ≪≫ Sigma.mapIso (g := V ∘ e) (fun ⟨a, b⟩ => w a b) ≪≫ Sigma.reindex e V

@[reassoc (attr := simp)]
lemma dgBarCoproductDecompositionIso_ι (a : A) (b : B a) :
    Sigma.ι (W a) b ≫ Sigma.ι (fun a => ∐ W a) a ≫
      (dgBarCoproductDecompositionIso R V W e w).hom =
        (w a b).hom ≫ Sigma.ι V (e ⟨a, b⟩) := by
  simp [dgBarCoproductDecompositionIso, sigmaSigmaIso]

def dgBarCoproductDecompositionCofan : Cofan (fun a => ∐ W a) :=
  Cofan.mk (∐ V) (fun a => Sigma.desc (fun b => (w a b).hom ≫ Sigma.ι V (e ⟨a, b⟩)))

def dgBarCoproductDecompositionIsColimit :
    IsColimit (dgBarCoproductDecompositionCofan R V W e w) := by
  have h : Sigma.desc (dgBarCoproductDecompositionCofan R V W e w).inj =
      (dgBarCoproductDecompositionIso R V W e w).hom := by
    apply Sigma.hom_ext
    intro a
    apply Sigma.hom_ext
    intro b
    simp [dgBarCoproductDecompositionCofan]
  letI : IsIso (Sigma.desc (dgBarCoproductDecompositionCofan R V W e w).inj) := by
    rw [h]
    infer_instance
  exact Cofan.isColimitOfIsIsoSigmaDesc _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
