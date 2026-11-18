module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanMooreChainMaps

/-!
# 元の Moore 正規化と実 Γ の零次数同型

概要：Moore の零次数包含と同じ DK counit から実 Γ の零次数を回収する。
方針：零次数は全部分対象であることと元の counit 同型を使う。
規約：元の Γ・N・counit を保つ。
使われ方：正規化 frame の零次数 augmentation 像の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]

def mooreDegreeZeroIso (W : SimplicialObject (ModuleCat.{u} R)) :
    ((normalizedMooreComplex (ModuleCat R)).obj W).X 0 ≅ W.obj (Opposite.op ⦋0⦌) :=
  asIso (⊤ : Subobject (W.obj (Opposite.op ⦋0⦌))).arrow

lemma mooreDegreeZeroIso_naturality {W V : SimplicialObject (ModuleCat.{u} R)} (f : W ⟶ V) :
    ((normalizedMooreComplex (ModuleCat R)).map f).f 0 ≫ (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso V).hom =
      (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).hom ≫ f.app (Opposite.op ⦋0⦌) :=
  _root_.SerrePositivity.ComplexLimits.normalizedMoore_map_arrow f 0

lemma mooreDegreeZeroIso_inv_naturality {W V : SimplicialObject (ModuleCat.{u} R)} (f : W ⟶ V) :
    f.app (Opposite.op ⦋0⦌) ≫ (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso V).inv =
      (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv ≫ ((normalizedMooreComplex (ModuleCat R)).map f).f 0 := by
  apply (cancel_mono (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso V).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso_naturality, Iso.inv_hom_id_assoc]

def gammaDegreeZeroIso (L : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)).obj L).obj
      (Opposite.op ⦋0⦌) ≅ L.X 0 :=
  (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (Abelian.DoldKan.Γ.obj L)).symm ≪≫
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) 0).mapIso
      ((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
        ChainComplex (ModuleCat R) ℕ).counitIso.app L)

end SerrePositivity.ComplexLimits
