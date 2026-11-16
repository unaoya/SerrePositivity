module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.Components
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# 行ごとに分裂する短複体の指定積全複体

## 概要
横次数ごとに分裂する短複体は、指定積全複体の各次数でも分裂する。

## 方針
元の行射影と分裂の射から、積の指定持ち上げで次数ごとの分裂を作る。

## 規約
行の分裂が横微分と可換であるとは仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部と尾部の短完全列。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 同じ指定積全複体関手の加法性。 -/
instance total_additive : (cochainProductTotalizationFunctor (ModuleCat.{u} R)).Additive where
  map_add {K M} f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply component_hom_ext
    intro n
    simp only [HomologicalComplex.add_f_apply, Preadditive.add_comp,
      componentπ_naturality, Preadditive.comp_add]

variable (S : ShortComplex (CochainComplex (Complex R) ℕ))
    (hS : ∀ n : ℕ, (S.map (HomologicalComplex.eval (Complex R) (.up ℕ) n)).Splitting)

/-- 各行の分裂から取る、全複体の各次数での引き戻し。 -/
def totalDegreeRetraction (q : ℤ) : (total S.X₂).X q ⟶ (total S.X₁).X q :=
  componentLift S.X₁ q (fun n => componentπ S.X₂ n q ≫ (hS n).r.f (q-n))

/-- 各行の分裂から取る、全複体の各次数での切断。 -/
def totalDegreeSection (q : ℤ) : (total S.X₃).X q ⟶ (total S.X₂).X q :=
  componentLift S.X₂ q (fun n => componentπ S.X₃ n q ≫ (hS n).s.f (q-n))

/-- 指定積全複体の各次数での、元の行の分裂を使う分裂。 -/
def totalDegreeSplitting (q : ℤ) :
    ((S.map (cochainProductTotalizationFunctor (ModuleCat.{u} R))).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) q)).Splitting where
  r := totalDegreeRetraction S hS q
  s := totalDegreeSection S hS q
  f_r := by
    change ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map S.f).f q ≫
      totalDegreeRetraction S hS q = 𝟙 ((total S.X₁).X q)
    apply component_hom_ext
    intro n
    dsimp only [totalDegreeRetraction]
    simp only [Category.assoc, componentLift_π, componentLift_π_assoc,
      componentπ_naturality, componentπ_naturality_assoc, Category.id_comp]
    have hn := congrArg (fun f => f.f (q-n)) (hS n).f_r
    change (S.f.f n).f (q-n) ≫ (hS n).r.f (q-n) = 𝟙 ((S.X₁.X n).X (q-n)) at hn
    rw [hn, Category.comp_id]
  s_g := by
    change totalDegreeSection S hS q ≫
      ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map S.g).f q = 𝟙 ((total S.X₃).X q)
    apply component_hom_ext
    intro n
    dsimp only [totalDegreeSection]
    simp only [Category.assoc, componentLift_π, componentLift_π_assoc,
      componentπ_naturality, componentπ_naturality_assoc, Category.id_comp]
    have hn := congrArg (fun f => f.f (q-n)) (hS n).s_g
    change (hS n).s.f (q-n) ≫ (S.g.f n).f (q-n) = 𝟙 ((S.X₃.X n).X (q-n)) at hn
    rw [hn, Category.comp_id]
  id := by
    change totalDegreeRetraction S hS q ≫
      ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map S.f).f q +
        ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map S.g).f q ≫
          totalDegreeSection S hS q = 𝟙 ((total S.X₂).X q)
    apply component_hom_ext
    intro n
    dsimp only [totalDegreeRetraction, totalDegreeSection]
    simp only [Preadditive.add_comp, Category.assoc, componentLift_π, componentLift_π_assoc,
      componentπ_naturality, componentπ_naturality_assoc, Category.id_comp]
    let rn : S.X₂.X n ⟶ S.X₁.X n := (hS n).r
    let sn : S.X₃.X n ⟶ S.X₂.X n := (hS n).s
    have hn : rn.f (q-n) ≫ (S.f.f n).f (q-n) +
        (S.g.f n).f (q-n) ≫ sn.f (q-n) = 𝟙 ((S.X₂.X n).X (q-n)) :=
      congrArg (fun f => f.f (q-n)) (hS n).id
    change componentπ S.X₂ n q ≫ (rn.f (q-n) ≫ (S.f.f n).f (q-n)) +
      componentπ S.X₂ n q ≫ ((S.g.f n).f (q-n) ≫ sn.f (q-n)) = componentπ S.X₂ n q
    rw [← Preadditive.comp_add, hn, Category.comp_id]

include hS in
/-- 行ごとの分裂だけで、指定積全複体の短完全性が従う。 -/
theorem total_shortExact_of_rowSplitting :
    (S.map (cochainProductTotalizationFunctor (ModuleCat.{u} R))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun q => (totalDegreeSplitting S hS q).shortExact)

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
