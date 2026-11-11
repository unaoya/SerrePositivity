module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPiConnectivity
public import SerrePositivity.KST.LocalizingInvariants.StableValueFunctor
public import SerrePositivity.KST.LocalizingInvariants.Invariant

/-!
概要：連結な基礎模型上の k-connective 不変量の条件と、レベル射への適用を記述する。
方針：基礎スペクトルと実安定圏の供給関手を明示し、同じ射の整数 π の条件を使う。
規約：代数の供給・pro レベル表示の存在は入力せず主張もしない。
使われ方：LT Def. 2.5 の基礎模型界面と、既に連結なレベル表示への適用。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants

variable {C : Type v} [Category.{w} C]
  (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}) (U : C ⥤ hoFunctor.obj Sp.{u})
  (P : C ⥤ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})

def IsKConnectiveOn (k : ℤ) : Prop :=
  IsLocalizingInvariant Φ ∧ (∀ X : C, SpectrumHo.IsPiConnective (U.obj X) 0) ∧
    ∀ {X Y : C} (f : X ⟶ Y) (n : ℤ), 1 ≤ n →
      SpectrumHo.IsPiZeroIso (U.map f) → SpectrumHo.IsPiConnected (U.map f) n →
        SpectrumHo.IsPiConnected ((P ⋙ stableValueFunctor Φ).map f) (n + k)

lemma IsKConnectiveOn.levelMap_connected {k n : ℤ}
    (h : IsKConnectiveOn Φ U P k) {X Y : ProExcision.Tower C}
    (f : ProExcision.LevelHom X Y) (hn : 1 ≤ n)
    (hc : ∀ m, SpectrumHo.IsPiConnected (U.map (f.app m)) n) :
    ProSpectrum.IsPiProConnected (f.map (P ⋙ stableValueFunctor Φ)) (n + k) := by
  apply ProSpectrum.piProConnected_of_levelwise
  intro m
  exact h.2.2 (f.app m) n hn ((hc m).piZeroIso hn) (hc m)

end SerrePositivity.KST.LocalizingInvariants
