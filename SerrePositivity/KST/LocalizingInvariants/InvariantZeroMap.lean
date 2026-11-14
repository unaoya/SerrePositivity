module

public import SerrePositivity.KST.LocalizingInvariants.StableValueFunctor
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.KST.LocalizingInvariants.SpectrumZeroClass

/-!
概要：全対象を零化する完全関手の不変量の像は、元の値の h Sp の零射。
方針：零安定圏を経由する関手へ自然同型で比較し、不変量の零保存を使う。
規約：元の完全関手を変更しない。使われ方：Tamme の二つの射影と両包含の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)

include hΦ in
lemma valueMap_hom_zero_of_zero_values {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hF : ∀ a, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) a)) :
    SpectrumHo.hom (valueMap Φ F) = 0 := by
  let G : A ⟶ B := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory) ≫ fromZeroCategory B
  have hG : ∀ a, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (G.hom.app (Opposite.op ⦋0⦌) a) := by
    intro a
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A).hom ≫ (fromZeroCategory B).hom).app _ a)
    rw [throughZero_hom, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex B.obj).isZero
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ hF hG
  have hz : IsZero ((stableValueFunctor Φ).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u}) := by
    have h := hΦ.preservesZero _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero
    rw [← value_vertex Φ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory] at h
    exact h.isZeroHo
  calc
    SpectrumHo.hom (valueMap Φ F) = (stableValueFunctor Φ).map G :=
      valueMap_hom_eq_of_functorIso Φ e
    _ = (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A) ≫
        (stableValueFunctor Φ).map (fromZeroCategory B) := Functor.map_comp _ _ _
    _ = 0 := by rw [hz.eq_zero_of_tgt ((stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A)), zero_comp]

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
