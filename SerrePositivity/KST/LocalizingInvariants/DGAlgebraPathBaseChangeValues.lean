module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeNonpositive
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantQuasiIso

/-!
概要：指定された底経路に沿う通常底変更の実比較を、元の実不変量値の同型へ送る。
方針：非正次数共通模型への両準同型を反転し、元の底・上段の値の射を保つ。
規約：任意の底変更不変性を入力しない。使われ方：roof の右三角形と実値の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
variable (R : Type u) [CommRing R] {P B U : Mon (Complex R)}
  (a b : P ⟶ B) (q : U ⟶ B) (w : Path.Witness R a b)
  [P.X.IsStrictlyLE 0] [U.X.IsStrictlyLE 0] [Epi q.hom]
  (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

attribute [local instance] firstPullback_nonpositive secondPullback_nonpositive

lemma firstNonpositive_value_isIso {k : ℤ} (h : IsKConnective R Φ k) :
    IsIso ((invariantFunctor R Φ).map (firstNonpositive R a q)) :=
  h.quasiIso_value_isIso R Φ
    (by change (MonoidPullback.obj a q).X.IsLE 0; infer_instance)
    (connectiveCover_isConnective R _) _ (firstNonpositive_quasiIso R a q)

lemma secondNonpositive_value_isIso {k : ℤ} (h : IsKConnective R Φ k) :
    IsIso ((invariantFunctor R Φ).map (secondNonpositive R a b q w)) :=
  h.quasiIso_value_isIso R Φ
    (by change (MonoidPullback.obj b q).X.IsLE 0; infer_instance)
    (connectiveCover_isConnective R _) _ (secondNonpositive_quasiIso R a b q w)

def valueIso {k : ℤ} (h : IsKConnective R Φ k) :
    (invariantFunctor R Φ).obj (MonoidPullback.obj a q) ≅
      (invariantFunctor R Φ).obj (MonoidPullback.obj b q) := by
  have := firstNonpositive_value_isIso R a q Φ h
  have := secondNonpositive_value_isIso R a b q w Φ h
  exact asIso ((invariantFunctor R Φ).map (firstNonpositive R a q)) ≪≫
    (asIso ((invariantFunctor R Φ).map (secondNonpositive R a b q w))).symm

lemma valueIso_base {k : ℤ} (h : IsKConnective R Φ k) :
    (valueIso R a b q w Φ h).hom ≫ (invariantFunctor R Φ).map (MonoidPullback.fst b q) =
      (invariantFunctor R Φ).map (MonoidPullback.fst a q) := by
  have := secondNonpositive_value_isIso R a b q w Φ h
  have he : (invariantFunctor R Φ).map (MonoidPullback.fst b q) =
      (invariantFunctor R Φ).map (secondNonpositive R a b q w) ≫
        (invariantFunctor R Φ).map (nonpositiveBase R a q) := by
    rw [← Functor.map_comp, secondNonpositive_base]
  change ((invariantFunctor R Φ).map (firstNonpositive R a q) ≫
    inv ((invariantFunctor R Φ).map (secondNonpositive R a b q w))) ≫ _ = _
  rw [he, Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp, firstNonpositive_base]

lemma valueIso_upper {k : ℤ} (h : IsKConnective R Φ k) :
    (valueIso R a b q w Φ h).hom ≫ (invariantFunctor R Φ).map (MonoidPullback.snd b q) =
      (invariantFunctor R Φ).map (MonoidPullback.snd a q) := by
  have := secondNonpositive_value_isIso R a b q w Φ h
  have he : (invariantFunctor R Φ).map (MonoidPullback.snd b q) =
      (invariantFunctor R Φ).map (secondNonpositive R a b q w) ≫
        (invariantFunctor R Φ).map (nonpositiveUpper R a q) := by
    rw [← Functor.map_comp, secondNonpositive_upper]
  change ((invariantFunctor R Φ).map (firstNonpositive R a q) ≫
    inv ((invariantFunctor R Φ).map (secondNonpositive R a b q w))) ≫ _ = _
  rw [he, Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp, firstNonpositive_upper]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
