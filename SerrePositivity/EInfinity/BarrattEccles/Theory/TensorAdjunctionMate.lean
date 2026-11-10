module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.LaxTensorComparison

/-!
# モノイダル随伴の下での比較射の随伴像

## 概要
HA §3.2.2 の厳密な係数変更で、テンソルに関する二つの代数作用を比べる。

## 方針
右随伴の tensorator の随伴像を左随伴の余積構造で表す。

## 規約
ここでは左随伴のテンソル比較の可逆性を使わない。

## 使われ方
オペラッドの係数拡大と係数制限の随伴。
-/

@[expose] public noncomputable section

universe u v u' v'

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (A : L ⊣ R)
  [R.LaxMonoidal]

section Oplax

variable [L.OplaxMonoidal] [A.IsMonoidal]

/-- 単位対象の tensorator の随伴像は余単位対象の比較。 -/
lemma laxUnit_mate :
    (A.homEquiv (𝟙_ C) (𝟙_ D)).symm (ε R) = η L := by
  rw [A.homEquiv_counit, A.map_ε_comp_counit_app_unit]

/-- 二つの比較射の tensorator の随伴像を、各比較射の随伴像で表す。 -/
lemma laxTensorComparison_mate {X Y : C} {U V : D}
    (a : X ⟶ R.obj U) (b : Y ⟶ R.obj V) :
    (A.homEquiv (X ⊗ Y) (U ⊗ V)).symm (laxTensorComparison R a b) =
      δ L X Y ≫ ((A.homEquiv X U).symm a ⊗ₘ (A.homEquiv Y V).symm b) := by
  simp only [laxTensorComparison, A.homEquiv_counit, L.map_comp, Category.assoc,
    A.map_μ_comp_counit_app_tensor]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc]
  congr 1
  exact tensorHom_comp_tensorHom _ _ _ _

end Oplax

/-- 強モノイダル関手のテンソル冪の比較は同型。 -/
lemma laxPowerComparison_isIso (F : C ⥤ D) [F.Monoidal] (K : C) (n : ℕ) :
    IsIso (laxPowerComparison F K n) := by
  induction n with
  | zero =>
    rw [laxPowerComparison]
    exact (Functor.Monoidal.εIso F).isIso_hom
  | succ n ih =>
    rw [laxPowerComparison]
    let e := (tensorLeft (F.obj K)).mapIso (asIso (laxPowerComparison F K n)) ≪≫
      Functor.Monoidal.μIso F K (power K n)
    exact e.isIso_hom

/-- 係数変更随伴とテンソル冪の比較は可換。 -/
lemma laxPowerComparison_mate [L.Monoidal] [A.IsMonoidal] {K : C} {U : D}
    (a : L.obj K ⟶ U) (n : ℕ) :
    laxPowerComparison L K n ≫
      (A.homEquiv (power K n) (power U n)).symm
        (TensorPowers.map ((A.homEquiv K U) a) n ≫ laxPowerComparison R U n) =
      TensorPowers.map a n := by
  induction n with
  | zero =>
    change ε L ≫ (A.homEquiv (𝟙_ C) (𝟙_ D)).symm (𝟙 _ ≫ ε R) = 𝟙 _
    rw [Category.id_comp, laxUnit_mate A, Functor.Monoidal.ε_η]
  | succ n ih =>
    simp only [laxPowerComparison, TensorPowers.map, power]
    rw [Category.assoc, tensorHom_comp_whiskerLeft_assoc]
    change (L.obj K ◁ laxPowerComparison L K n) ≫ μ L K (power K n) ≫
      (A.homEquiv _ _).symm (laxTensorComparison R ((A.homEquiv K U) a)
        (TensorPowers.map ((A.homEquiv K U) a) n ≫ laxPowerComparison R U n)) = _
    rw [laxTensorComparison_mate A, Functor.Monoidal.μ_δ_assoc, Equiv.symm_apply_apply]
    rw [whiskerLeft_comp_tensorHom, ih]

end SerrePositivity.EInfinity
