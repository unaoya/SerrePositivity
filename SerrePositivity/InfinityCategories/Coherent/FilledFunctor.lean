module

public import SerrePositivity.InfinityCategories.Coherent.FilledHom
public import SerrePositivity.InfinityCategories.Coherent.UnitComposition

/-!
# Kan 延長から豊穣関手への復元

概要：既知の面を固定する端点 Hom の延長から thickening 上の豊穣関手を復元する。
方針：全ての対象対の Hom を取り、空の区間、真部分区間、全区間の合成を場合分けする。
規約：全区間の端点を経由する退化した合成は単位則で処理する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10 のホーン充填単体。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialThickening MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Coherent

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {n : ℕ} {i : Fin (n + 3)}

/-- 概要：充填用の Hom 写像は全ての三対象について合成を保つ。
方針：順序外は空性、外側が真部分区間なら既知の合成則、全区間なら面の制限と単位則を使う。
規約：延長の制限条件は Kan 延長から得られる具体的な条件。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10 の豊穣関手の合成則。 -/
lemma hornFillHom_comp
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g)
    (hg : ∀ j, (pathHollowFace (hornHollowPoint.{v} i h0 hn) j).ι ≫ g =
      hornHollowFaceHom σ h0 hn j) (a b c : Fin (n + 3)) :
    pathCompMap (ULift.up.{v} a) (ULift.up b) (ULift.up c) ≫ hornFillHom σ h0 hn g a c =
    (hornFillHom σ h0 hn g a b ⊗ₘ hornFillHom σ h0 hn g b c) ≫
      SimplicialCategory.sHomComp (hornObj σ a) (hornObj σ b) (hornObj σ c) := by
  by_cases hab : a ≤ b
  swap
  · exact pathProduct_empty_hom_ext (ULift.up.{v} a) (ULift.up b) (ULift.up c) (Or.inl hab) _ _
  by_cases hbc : b ≤ c
  swap
  · exact pathProduct_empty_hom_ext (ULift.up.{v} a) (ULift.up b) (ULift.up c) (Or.inr hbc) _ _
  by_cases hpac : a ≠ 0 ∨ c ≠ Fin.last (n + 2)
  · have hpab : a ≠ 0 ∨ b ≠ Fin.last (n + 2) := by
      rcases hpac with ha | hc
      · exact Or.inl ha
      · right
        intro hb
        exact hc (le_antisymm (Fin.le_last c) (hb ▸ hbc))
    have hpbc : b ≠ 0 ∨ c ≠ Fin.last (n + 2) := by
      rcases hpac with ha | hc
      · left
        intro hb
        exact ha (le_antisymm (hb ▸ hab) (Fin.zero_le a))
      · exact Or.inr hc
    rw [hornFillHom_proper σ h0 hn g a c (hab.trans hbc) hpac,
      hornFillHom_proper σ h0 hn g a b hab hpab,
      hornFillHom_proper σ h0 hn g b c hbc hpbc]
    exact hornProperIntervalHom_comp σ h0 hn a b c hab hbc hpab hpbc hpac
  have ha : a = 0 := not_not.mp (fun h ↦ hpac (Or.inl h))
  have hc : c = Fin.last (n + 2) := not_not.mp (fun h ↦ hpac (Or.inr h))
  subst a c
  by_cases hb0 : b = 0
  · subst b
    exact pathHom_comp_left_unit _ _ _ _ _ _ (hornFillHom_id σ h0 hn g 0)
  by_cases hbn : b = Fin.last (n + 2)
  · subst b
    exact pathHom_comp_right_unit _ _ _ _ _ _
      (hornFillHom_id σ h0 hn g (Fin.last (n + 2)))
  exact hornFillHom_comp_inner σ h0 hn g hg b
    (lt_of_le_of_ne (Fin.zero_le b) (Ne.symm hb0)) (lt_of_le_of_ne (Fin.le_last b) hbn)

/-- 概要：端点 Hom の延長と既知区間の回収から thickening 上の豊穣関手を構成する。
方針：対象には回収した対象族、射には充填用の Hom を使い、単位則と合成則を添える。
規約：Mathlib の SimplicialNerve の単体そのものの型で構成する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10 の内部ホーンの充填候補。 -/
noncomputable def hornFilledFunctor
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g)
    (hg : ∀ j, (pathHollowFace (hornHollowPoint.{v} i h0 hn) j).ι ≫ g =
      hornHollowFaceHom σ h0 hn j) :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{v} (Fin (n + 3)))) C where
  obj X := hornObj σ X.as.down
  map X Y := hornFillHom σ h0 hn g X.as.down Y.as.down
  map_id X := hornFillHom_id σ h0 hn g X.as.down
  map_comp X Y Z := hornFillHom_comp σ h0 hn g hg X.as.down Y.as.down Z.as.down

end SerrePositivity.InfinityCategories.Coherent
