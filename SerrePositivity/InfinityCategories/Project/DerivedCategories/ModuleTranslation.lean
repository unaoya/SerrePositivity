module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModuleSphereNaturality
/-!
概要：全頂点への加法による実単体的同型。
方針：元の射と全基点の誘導写像を保ち、既存の実 Whitehead 逆へ接続する。
規約：可換性・平坦性を仮定しない。使われ方：β5(g) の正規化界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable (W : SimplicialObject (ModuleCat.{v} S))
def moduleVertexConstant (x : W.obj (op ⦋0⦌)) (n : SimplexCategoryᵒᵖ) : W.obj n :=
  (W.map (n.unop.const ⦋0⦌ 0).op).hom x
lemma moduleVertexConstant_naturality (x : W.obj (op ⦋0⦌))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (W.map φ).hom (moduleVertexConstant W x n) = moduleVertexConstant W x m := by
  dsimp only [moduleVertexConstant]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp]
  rfl
lemma moduleVertexConstant_zero (x : W.obj (op ⦋0⦌)) :
    moduleVertexConstant W x (op ⦋0⦌) = x := by
  dsimp only [moduleVertexConstant]
  rw [SimplexCategory.const_eq_id, op_id, W.map_id]
  rfl
def moduleTranslationHom (x : W.obj (op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W where
  app n := ↾fun z : W.obj n ↦ z + moduleVertexConstant W x n
  naturality n m φ := by
    ext z
    let t : W.obj n := z
    symm
    change (W.map φ).hom (t + moduleVertexConstant W x n) = _
    rw [map_add, moduleVertexConstant_naturality]
    rfl
def moduleTranslationIso (x : W.obj (op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W ≅ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W where
  hom := moduleTranslationHom W x
  inv := moduleTranslationHom W (-x)
  hom_inv_id := by
    ext n z
    let t : W.obj n := z
    change (t + moduleVertexConstant W x n) + moduleVertexConstant W (-x) n = t
    simp only [moduleVertexConstant, map_neg, add_neg_cancel_right]
  inv_hom_id := by
    ext n z
    let t : W.obj n := z
    change (t + moduleVertexConstant W (-x) n) + moduleVertexConstant W x n = t
    simp only [moduleVertexConstant, map_neg, neg_add_cancel_right]
lemma moduleTranslationIso_zero (x : W.obj (op ⦋0⦌)) :
    (moduleTranslationIso W x).hom.app (op ⦋0⦌) 0 = x := by
  change (0 : W.obj (op ⦋0⦌)) + moduleVertexConstant W x (op ⦋0⦌) = x
  rw [zero_add, moduleVertexConstant_zero]
variable {W} {V : SimplicialObject (ModuleCat.{v} S)}
lemma moduleVertexConstant_map (f : W ⟶ V) (x : W.obj (op ⦋0⦌))
    (n : SimplexCategoryᵒᵖ) :
    (f.app n).hom (moduleVertexConstant W x n) =
      moduleVertexConstant V ((f.app (op ⦋0⦌)).hom x) n := by
  exact (congrArg (fun ψ ↦ ψ.hom x) (f.naturality (n.unop.const ⦋0⦌ 0).op))
lemma moduleTranslationIso_naturality (f : W ⟶ V) (x : W.obj (op ⦋0⦌)) :
    (moduleTranslationIso W x).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f ≫
        (moduleTranslationIso V ((f.app (op ⦋0⦌)).hom x)).hom := by
  ext n z
  let t : W.obj n := z
  change (f.app n).hom (t + moduleVertexConstant W x n) = _
  rw [map_add, moduleVertexConstant_map]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
