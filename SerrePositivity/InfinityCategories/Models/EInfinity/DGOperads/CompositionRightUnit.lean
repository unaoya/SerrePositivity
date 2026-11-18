module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentFactor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionBlocks
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionRightUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorUnitFamily

/-!
模型。文献の定義との比較は後で
# 全入力への単位演算の代入

概要：Berger–Moerdijk §1 の部分合成の右単位則を、先頭の任意個の入力への反復合成へ拡張する。
方針：最後の単位演算を除いてから前半へ帰納仮定を適用し、単位族の縮約と比較する。
規約：未処理の末尾入力を任意個残す。
使われ方：Schur 代数が生成元で生成されることと自由・忘却随伴の逆律を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso

/-- 概要：最後の指定入力への単位演算の代入は係数の arity の移送だけになる（Berger–Moerdijk §1）。
方針：単位演算を係数の移送に通し、部分合成の右単位則を使う。
規約：n+1+k と n+(k+1) の表示の違いを移送で残す。
使われ方：全ての内側演算が単位の場合の帰納段階で一段の合成を除く。 -/
lemma composeFirstInputInsertion_unit (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) :
    (P.arity (n + 1 + k) ◁ P.unit) ≫ P.composeFirstInputInsertion n k 1 =
      (ρ_ (P.arity (n + 1 + k))).hom ≫
        eqToHom (congrArg P.arity (by omega : n + 1 + k = n + (k + 1))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion
  rw [whisker_exchange_assoc]
  erw [reassoc_of% (P.comp_unit (n + k) ⟨n, by omega⟩)]
  rw [rightUnitor_naturality_assoc]
  simp only [eqToHom_trans]

/-- 概要：先頭の全ての指定入力へ単位演算を代入すると単位族の縮約だけになる（Berger–Moerdijk §1）。
方針：最後の係数を単位則で除き、前半の反復合成へ帰納仮定を適用する。
規約：空の指定入力族と任意の末尾入力数 k を含む。
使われ方：自由代数の演算を生成元の包含に制限したときの式を与える。 -/
lemma composeFirstInputs_units (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) :
    (P.arity (n + k) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun _ : Fin n => P.unit)) ≫
      P.composeFirstInputs n k (fun _ => 1) =
    (P.arity (n + k) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).hom) ≫ (ρ_ (P.arity (n + k))).hom ≫
      eqToHom (congrArg P.arity (by simp : n + k = (∑ _ : Fin n, 1) + k)) := by
  induction n generalizing k with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso, Iso.refl_hom,
      Fin.sum_univ_zero, eqToHom_refl, whiskerLeft_id, Category.id_comp, Category.comp_id]
  | succ n ih =>
    have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_naturality n
      (V := fun _ : Fin (n + 1) => 𝟙_ (Complex A))
      (W := fun _ : Fin (n + 1) => P.arity 1) (fun _ => P.unit)
    rw [P.composeFirstInputs_oneSlot_after_factor, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso_succ_hom]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← whiskerLeft_comp_assoc, hm]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [tensorHom_def]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_last (P.composeFirstInputInsertion n k 1)
      (P.composeFirstInputs n (k + 1) (fun _ => 1)) P.unit)]
    have hmid := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_middle
      ((P.arity (n + 1 + k) ◁ P.unit) ≫ P.composeFirstInputInsertion n k 1)
      (P.composeFirstInputs n (k + 1) (fun _ => 1))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun _ : Fin n => P.unit))
    simp only [tensorHom_id] at hmid
    rw [reassoc_of% hmid, P.composeFirstInputInsertion_unit, ih (k + 1)]
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
    simp only [Category.assoc]
    erw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitution_rightUnit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).hom
      (eqToHom (congrArg P.arity (by omega : n + 1 + k = n + (k + 1)))))]
    simp only [whiskerLeft_comp, Category.assoc, eqToHom_trans]

/-- 概要：全入力への単位演算の合成は元の演算を返す（Berger–Moerdijk §1）。
方針：末尾を残した反復合成の右単位則へ末尾長さ零を適用する。
規約：内側の係数のテンソル単位族は専用の縮約同型で一つにまとめる。
使われ方：Schur 代数の各 arity の生成射を生成元への作用として表す。 -/
lemma composition_units (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) :
    (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun _ : Fin n => P.unit)) ≫
      P.composition n (fun _ => 1) =
    (P.arity n ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).hom) ≫ (ρ_ (P.arity n)).hom ≫
      eqToHom (congrArg P.arity (by simp : n = ∑ _ : Fin n, 1)) := by
  simpa only [Nat.add_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composition, eqToHom_refl, id_whiskerRight, Category.id_comp,
    Category.comp_id] using P.composeFirstInputs_units n 0

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
