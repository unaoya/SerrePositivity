module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.SinglePairingValue

/-!
# 離散複体の単位値による射の比較

概要：離散複体への単位射を元の加群の値で判定する。
方針：単位射と閉元の同値と single の標準成分同型を使う。
規約：元の single 関手と任意の可換基礎環を保持する。
使われ方：標準 H⁰ 同型の単位・積の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomologyZero
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma singleValue_injective (M : ModuleCat.{u} A) : Function.Injective (_root_.SerrePositivity.HomologyZero.singleValue M) := by
  intro f g h
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  exact ((ModuleCat.mono_iff_injective (singleObjXSelf (.up ℤ) 0 M).hom).mp
    inferInstance) h

lemma singleValue_map (M N : ModuleCat.{u} A) (μ : M ⟶ N)
    (f : 𝟙_ (Complex A) ⟶ _root_.SerrePositivity.cochainSingleZero M) :
    _root_.SerrePositivity.HomologyZero.singleValue N (f ≫ (CochainComplex.singleFunctor (ModuleCat A) 0).map μ) =
      μ (_root_.SerrePositivity.HomologyZero.singleValue M f) := by
  unfold _root_.SerrePositivity.HomologyZero.singleValue
  rw [cycleFromUnit_postcomp]
  change (singleObjXSelf (.up ℤ) 0 N).hom
    (((single (ModuleCat A) (.up ℤ) 0).map μ).f 0 (cycleFromUnit _ f).val) = _
  rw [single_map_f_self]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.inv_hom_id_apply]

lemma singleValue_identity :
    _root_.SerrePositivity.HomologyZero.singleValue (ModuleCat.of A A) (𝟙 (𝟙_ (Complex A))) = (1 : A) := rfl

end SerrePositivity.HomologyZero
