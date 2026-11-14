module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Resolution.FixedObject
public import SerrePositivity.DifferentialGraded.Resolution.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Filtered.Final
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
# Resolution.Cell

## 概要
13 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## CellSequence（旧 SerrePositivity/DifferentialGraded/Resolution/CellSequence.lean） -/

/-! # 同じ対象ラベル上で全境界cellを付加する反復列

## 概要
全段階の豊穣構造はMathlibのEnrichedCategoryであり、対象型Dの既存instanceは変更しない。
ここでは各対象対のHom列とその増大を構成する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CellSequence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def initial : FixedObjectAugmentation A D D id where
  category := (inferInstance : DGCategory A (DGCategoryCycleCover.Source A D))
  map x y := (DGCategoryCycleCover.augmentation A D).map x y
  map_id x := (DGCategoryCycleCover.augmentation A D).map_id x
  map_comp x y z := (DGCategoryCycleCover.augmentation A D).map_comp x y z

lemma initial_homKFlat : (initial A D).HomKFlat := DGCategoryCycleCover.source_homKFlat A D

def stage : ℕ → FixedObjectAugmentation A D D id
  | 0 => initial A D
  | n + 1 => (stage n).attach

lemma stage_homKFlat (n : ℕ) : (stage A D n).HomKFlat := by
  induction n with
  | zero => exact initial_homKFlat A D
  | succ n ih => exact (stage A D n).attach_homKFlat ih

abbrev stageHom (n : ℕ) (x y : D) : Complex A := (stage A D n).category.Hom x y

def transition (n : ℕ) (x y : D) : stageHom A D n x y ⟶ stageHom A D (n + 1) x y :=
  (stage A D n).transition x y

def stageAugmentation (n : ℕ) (x y : D) : stageHom A D n x y ⟶ homObject A D x y :=
  (stage A D n).map x y

lemma transition_augmentation (n : ℕ) (x y : D) :
    transition A D n x y ≫ stageAugmentation A D (n + 1) x y = stageAugmentation A D n x y :=
  (stage A D n).transition_augmentation x y

def homDiagram (x y : D) : ℕ ⥤ Complex A := Functor.ofSequence (fun n => transition A D n x y)

def augmentationCocone (x y : D) : Cocone (homDiagram A D x y) where
  pt := homObject A D x y
  ι := NatTrans.ofSequence (fun n => stageAugmentation A D n x y) (fun n => by
    change (homDiagram A D x y).map (homOfLE (Nat.le_succ n)) ≫
      stageAugmentation A D (n + 1) x y = stageAugmentation A D n x y ≫ 𝟙 _
    dsimp only [homDiagram]
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact transition_augmentation A D n x y)

lemma stage_fills (n : ℕ) (x y : D) (c : ComplexBoundaryCell A (stageAugmentation A D n x y)) :
    ∃ t : (stageHom A D (n + 1) x y).X c.degree,
      (stageHom A D (n + 1) x y).d c.degree (c.degree + 1) t =
        (transition A D n x y).f (c.degree + 1) c.cycle.val ∧
      (stageAugmentation A D (n + 1) x y).f c.degree t = c.primitive :=
  (stage A D n).attach_fills x y c

/-- 各対象対のHomの極限候補。豊穣単位・合成は後続で構成する。 -/
def candidateHom (x y : D) : Complex A := colimit (homDiagram A D x y)

def candidateAugmentation (x y : D) : candidateHom A D x y ⟶ homObject A D x y :=
  colimit.desc _ (augmentationCocone A D x y)

def stageInclusion (n : ℕ) (x y : D) : stageHom A D n x y ⟶ candidateHom A D x y :=
  colimit.ι (homDiagram A D x y) n

@[reassoc] lemma stageInclusion_augmentation (n : ℕ) (x y : D) :
    stageInclusion A D n x y ≫ candidateAugmentation A D x y = stageAugmentation A D n x y :=
  colimit.ι_desc _ _

@[reassoc] lemma transition_inclusion (n : ℕ) (x y : D) :
    transition A D n x y ≫ stageInclusion A D (n + 1) x y = stageInclusion A D n x y := by
  have h := colimit.w (homDiagram A D x y) (homOfLE (Nat.le_succ n))
  change (homDiagram A D x y).map (homOfLE (Nat.le_succ n)) ≫
    stageInclusion A D (n + 1) x y = stageInclusion A D n x y at h
  dsimp only [homDiagram] at h
  rw [Functor.ofSequence_map_homOfLE_succ] at h
  exact h

lemma candidateAugmentation_quasiIso (x y : D) : QuasiIso (candidateAugmentation A D x y) := by
  apply ComplexBoundaryCell.sequential_quasiIso A (homDiagram A D x y)
    (colimit.cocone _) (augmentationCocone A D x y) (colimit.isColimit _)
  intro n c
  change ComplexBoundaryCell A (stageAugmentation A D n x y) at c
  change ∃ t : (stageHom A D (n + 1) x y).X c.degree,
    (stageHom A D (n + 1) x y).d c.degree (c.degree + 1) t =
      ((homDiagram A D x y).map (homOfLE (Nat.le_succ n))).f (c.degree + 1) c.cycle.val ∧
    (stageAugmentation A D (n + 1) x y).f c.degree t = c.primitive
  dsimp only [homDiagram]
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact stage_fills A D n x y c

lemma candidateHom_kFlat (x y : D) : complexKFlat A (candidateHom A D x y) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact complexKFlat_colimit A (homDiagram A D x y) (fun n => stage_homKFlat A D n x y)

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
end

end CellSequence

/-! ## CellComposition（旧 SerrePositivity/DifferentialGraded/Resolution/CellComposition.lean） -/

/-! # cell反復列のHom極限上の豊穣合成

## 概要
cell反復列のHom極限上の豊穣合成。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CellComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def candidateTensorIsColimit (x y z : D) :
    IsColimit ((colimit.cocone (homDiagram A D x y)).tensor
      (colimit.cocone (homDiagram A D y z))) := by
  letI : IsSifted ℕ := IsFiltered.isSifted
  exact (colimit.isColimit (homDiagram A D x y)).tensor (colimit.isColimit (homDiagram A D y z))

def compositionCocone (x y z : D) :
    Cocone (homDiagram A D x y ⊗ homDiagram A D y z) where
  pt := candidateHom A D x z
  ι := NatTrans.ofSequence
    (fun n => (stage A D n).category.comp x y z ≫ stageInclusion A D n x z) (fun n => by
      change ((homDiagram A D x y).map (homOfLE (Nat.le_succ n)) ⊗ₘ
        (homDiagram A D y z).map (homOfLE (Nat.le_succ n))) ≫
        ((stage A D (n + 1)).category.comp x y z ≫ stageInclusion A D (n + 1) x z) =
        ((stage A D n).category.comp x y z ≫ stageInclusion A D n x z) ≫ 𝟙 _
      dsimp only [homDiagram]
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ,
        Category.comp_id]
      have hc : (transition A D n x y ⊗ₘ transition A D n y z) ≫
          (stage A D (n + 1)).category.comp x y z =
          (stage A D n).category.comp x y z ≫ transition A D n x z :=
        ((stage A D n).transition_comp x y z).symm
      change (transition A D n x y ⊗ₘ transition A D n y z) ≫
        ((stage A D (n + 1)).category.comp x y z ≫ stageInclusion A D (n + 1) x z) =
        (stage A D n).category.comp x y z ≫ stageInclusion A D n x z
      rw [← Category.assoc, hc, Category.assoc, transition_inclusion])

def candidateComposition (x y z : D) :
    candidateHom A D x y ⊗ candidateHom A D y z ⟶ candidateHom A D x z :=
  (candidateTensorIsColimit A D x y z).desc (compositionCocone A D x y z)

lemma candidateComposition_stage (n : ℕ) (x y z : D) :
    (stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ≫ candidateComposition A D x y z =
      (stage A D n).category.comp x y z ≫ stageInclusion A D n x z :=
  (candidateTensorIsColimit A D x y z).fac (compositionCocone A D x y z) n

lemma candidateComposition_apply_stage (n : ℕ) (x y z : D) (p q k : ℤ) (hk : p + q = k)
    (a : (stageHom A D n x y).X p) (b : (stageHom A D n y z).X q) :
    (candidateComposition A D x y z).f k
      (ιTensorObj (candidateHom A D x y) (candidateHom A D y z) p q k hk
        ((stageInclusion A D n x y).f p a ⊗ₜ[A] (stageInclusion A D n y z).f q b)) =
    (stageInclusion A D n x z).f k
      (((stage A D n).category.comp x y z).f k
        (ιTensorObj (stageHom A D n x y) (stageHom A D n y z) p q k hk (a ⊗ₜ[A] b))) := by
  have h := congrArg (fun f => f.f k
    (ιTensorObj (stageHom A D n x y) (stageHom A D n y z) p q k hk (a ⊗ₜ[A] b)))
    (candidateComposition_stage A D n x y z)
  simpa only [chain_comp_apply, tensorMap_apply] using h

def candidateUnit (x : D) : 𝟙_ (Complex A) ⟶ candidateHom A D x x :=
  (stage A D 0).category.id x ≫ stageInclusion A D 0 x x

lemma candidateUnit_stage (n : ℕ) (x : D) :
    (stage A D n).category.id x ≫ stageInclusion A D n x x = candidateUnit A D x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (stage A D n).attach.category.id x ≫ stageInclusion A D (n + 1) x x = _
    have hi : (stage A D n).category.id x ≫ transition A D n x x =
        (stage A D (n + 1)).category.id x := (stage A D n).transition_id x
    rw [← hi, Category.assoc, transition_inclusion, ih]

lemma candidateUnit_augmentation (x : D) :
    candidateUnit A D x ≫ candidateAugmentation A D x x = eId (Complex A) x := by
  rw [candidateUnit, Category.assoc, stageInclusion_augmentation]
  exact (stage A D 0).map_id x

lemma candidateComposition_augmentation (x y z : D) :
    candidateComposition A D x y z ≫ candidateAugmentation A D x z =
    (candidateAugmentation A D x y ⊗ₘ candidateAugmentation A D y z) ≫
      eComp (Complex A) x y z := by
  apply (candidateTensorIsColimit A D x y z).hom_ext
  intro n
  change (stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ≫
    (candidateComposition A D x y z ≫ candidateAugmentation A D x z) =
    (stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ≫
      (candidateAugmentation A D x y ⊗ₘ candidateAugmentation A D y z) ≫ eComp (Complex A) x y z
  rw [← Category.assoc, candidateComposition_stage, Category.assoc, stageInclusion_augmentation,
    ← Category.assoc, tensorHom_comp_tensorHom, stageInclusion_augmentation,
    stageInclusion_augmentation]
  exact (stage A D n).map_comp x y z

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
end

end CellComposition

/-! ## CellUnits（旧 SerrePositivity/DifferentialGraded/Resolution/CellUnits.lean） -/

/-! # cell反復列の極限Homの左右単位則

## 概要
cell反復列の極限Homの左右単位則。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CellUnits
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma candidateComposition_left_unit (x y : D) :
    (λ_ (candidateHom A D x y)).inv ≫ candidateUnit A D x ▷ candidateHom A D x y ≫
      candidateComposition A D x x y = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply chain_ext_apply
  intro k a
  change (candidateComposition A D x x y).f k
    ((candidateUnit A D x ▷ candidateHom A D x y).f k
      ((λ_ (candidateHom A D x y)).inv.f k ((stageInclusion A D n x y).f k a))) =
    (stageInclusion A D n x y).f k a
  rw [← candidateUnit_stage A D n x, complexLeftUnitor_inv_apply, whiskerRight_apply,
    chain_comp_apply, candidateComposition_apply_stage]
  have h := congrArg (fun f : stageHom A D n x y ⟶ stageHom A D n x y => f.f k a)
    ((stage A D n).category.id_comp x y)
  change ((stage A D n).category.comp x x y).f k
    (((stage A D n).category.id x ▷ stageHom A D n x y).f k
      ((λ_ (stageHom A D n x y)).inv.f k a)) = a at h
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply] at h
  exact congrArg ((stageInclusion A D n x y).f k) h

lemma candidateComposition_right_unit (x y : D) :
    (ρ_ (candidateHom A D x y)).inv ≫ candidateHom A D x y ◁ candidateUnit A D y ≫
      candidateComposition A D x y y = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply chain_ext_apply
  intro k a
  change (candidateComposition A D x y y).f k
    ((candidateHom A D x y ◁ candidateUnit A D y).f k
      ((ρ_ (candidateHom A D x y)).inv.f k ((stageInclusion A D n x y).f k a))) =
    (stageInclusion A D n x y).f k a
  rw [← candidateUnit_stage A D n y, complexRightUnitor_inv_apply, whiskerLeft_apply,
    chain_comp_apply, candidateComposition_apply_stage]
  have h := congrArg (fun f : stageHom A D n x y ⟶ stageHom A D n x y => f.f k a)
    ((stage A D n).category.comp_id x y)
  change ((stage A D n).category.comp x y y).f k
    ((stageHom A D n x y ◁ (stage A D n).category.id y).f k
      ((ρ_ (stageHom A D n x y)).inv.f k a)) = a at h
  rw [complexRightUnitor_inv_apply, whiskerLeft_apply] at h
  exact congrArg ((stageInclusion A D n x y).f k) h

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
end

end CellUnits

/-! ## CellAssociativity（旧 SerrePositivity/DifferentialGraded/Resolution/CellAssociativity.lean） -/

/-! # cell反復列の極限Homの結合則

## 概要
cell反復列の極限Homの結合則。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CellAssociativity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma stageComposition_assoc (n : ℕ) (x y z t : D) :
    ((stage A D n).category.comp x y z ▷ stageHom A D n z t) ≫
      (stage A D n).category.comp x z t =
    (α_ (stageHom A D n x y) (stageHom A D n y z) (stageHom A D n z t)).hom ≫
      stageHom A D n x y ◁ (stage A D n).category.comp y z t ≫
        (stage A D n).category.comp x y t := by
  let : DGCategory A D := (stage A D n).category
  exact (e_assoc' (Complex A) x y z t).symm

def candidateTripleIsColimit (x y z t : D) :
    IsColimit (((colimit.cocone (homDiagram A D x y)).tensor
      (colimit.cocone (homDiagram A D y z))).tensor
        (colimit.cocone (homDiagram A D z t))) := by
  letI : IsSifted ℕ := IsFiltered.isSifted
  exact (candidateTensorIsColimit A D x y z).tensor (colimit.isColimit (homDiagram A D z t))

lemma candidateComposition_assoc (x y z t : D) :
    (candidateComposition A D x y z ▷ candidateHom A D z t) ≫ candidateComposition A D x z t =
    (α_ (candidateHom A D x y) (candidateHom A D y z) (candidateHom A D z t)).hom ≫
      candidateHom A D x y ◁ candidateComposition A D y z t ≫ candidateComposition A D x y t := by
  apply (candidateTripleIsColimit A D x y z t).hom_ext
  intro n
  apply HomologicalComplex.Hom.ext
  funext k
  apply SerrePositivity.cochainTensorTriple_hom_ext
    (stageHom A D n x y) (stageHom A D n y z) (stageHom A D n z t) k
  intro p q r hk
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro a b c
  change (candidateComposition A D x z t).f k
    ((candidateComposition A D x y z ▷ candidateHom A D z t).f k
      (((stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ⊗ₘ
          stageInclusion A D n z t).f k
        (ιTensorObj (stageHom A D n x y ⊗ stageHom A D n y z) (stageHom A D n z t)
          (p + q) r k hk
          (ιTensorObj (stageHom A D n x y) (stageHom A D n y z) p q (p + q) rfl
            (a ⊗ₜ[A] b) ⊗ₜ[A] c)))) =
    (candidateComposition A D x y t).f k
      ((candidateHom A D x y ◁ candidateComposition A D y z t).f k
        ((α_ (candidateHom A D x y) (candidateHom A D y z) (candidateHom A D z t)).hom.f k
          (((stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ⊗ₘ
              stageInclusion A D n z t).f k
            (ιTensorObj (stageHom A D n x y ⊗ stageHom A D n y z) (stageHom A D n z t)
              (p + q) r k hk
              (ιTensorObj (stageHom A D n x y) (stageHom A D n y z) p q (p + q) rfl
                (a ⊗ₜ[A] b) ⊗ₜ[A] c)))))
  simp only [tensorMap_apply, whiskerRight_apply, whiskerLeft_apply, associator_apply,
    candidateComposition_apply_stage]
  exact congrArg ((stageInclusion A D n x t).f k)
    (tensorComposition_assoc_apply
      (stageHom A D n x y) (stageHom A D n y z) (stageHom A D n z t)
      (stageHom A D n x z) (stageHom A D n y t) (stageHom A D n x t)
      ((stage A D n).category.comp x y z) ((stage A D n).category.comp x z t)
      ((stage A D n).category.comp y z t) ((stage A D n).category.comp x y t)
      (stageComposition_assoc A D n x y z t) p q r k hk a b c)

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
end

end CellAssociativity

/-! ## CellCategory（旧 SerrePositivity/DifferentialGraded/Resolution/CellCategory.lean） -/

/-! # 任意の小さいdg圏のK-flat解像度の構成

## 概要
初期cycle coverから全境界cellの付加を反復した極限。
元のHomのflatness、有界性、モデル構造又は比較定理の引用を仮定しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CellCategory
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

namespace DGCategoryCellResolution

def candidate : FixedObjectAugmentation A D D id where
  category := ofHomObjects A D (candidateHom A D) (candidateUnit A D) (candidateComposition A D)
    (candidateComposition_left_unit A D) (candidateComposition_right_unit A D)
    (fun a b c d => by rw [candidateComposition_assoc, Iso.inv_hom_id_assoc])
  map := candidateAugmentation A D
  map_id := candidateUnit_augmentation A D
  map_comp := candidateComposition_augmentation A D

abbrev Source : Type v := (candidate A D).Objects

def augmentation : DGFunctor A (Source A D) D := (candidate A D).augmentation

lemma source_homKFlat : localHomKFlat A (Source A D) :=
  (candidate A D).objects_homKFlat (candidateHom_kFlat A D)

lemma augmentation_homQuasiIso : HomQuasiIso (augmentation A D) :=
  fun x y => candidateAugmentation_quasiIso A D x.val y.val

lemma augmentation_essSurj : (augmentation A D).onHomotopy.EssSurj where
  mem_essImage Y := by
    let x : Source A D := ⟨ForgetEnrichment.to (C := D) (Complex A) Y.as⟩
    exact ⟨(toHomotopy A (Source A D)).obj (ForgetEnrichment.of (Complex A) x), ⟨Iso.refl _⟩⟩

lemma augmentation_quasiEquivalence : QuasiEquivalence (augmentation A D) :=
  ⟨augmentation_homQuasiIso A D, augmentation_essSurj A D⟩

def resolution : KFlatDGResolution.{u, v, v} A D where
  source := Source A D
  augmentation := augmentation A D
  quasiEquivalence := augmentation_quasiEquivalence A D
  homKFlat := source_homKFlat A D

end DGCategoryCellResolution

namespace KFlatDGResolution

/-- 全境界cell付加の逐次余極限による標準の指定K-flat dg圏解像度。 -/
def canonical : KFlatDGResolution.{u, v, v} A D := DGCategoryCellResolution.resolution A D

/-- 任意可換環上の任意の小さい非有界dg圏は、小さいK-flat dg圏解像度を持つ。 -/
theorem nonempty : Nonempty (KFlatDGResolution.{u, v, v} A D) := ⟨canonical A D⟩

end KFlatDGResolution
end SerrePositivity.DifferentialGraded
end

end CellCategory

/-! ## InitialStageComparison（旧 SerrePositivity/DifferentialGraded/Resolution/InitialStageComparison.lean） -/

/-! # 標準解像度の初期段階の増大比較

## 概要
標準解像度の初期段階の増大比較。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InitialStageComparison
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E]

lemma DGFunctor.hcongr_map {F G : DGFunctor A D E} (h : F = G) (x y : D) :
    HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

namespace DGCategoryCellResolution
variable (A D E) [Small.{u} D] [Small.{u} E] (F : DGFunctor A D E)

def initialComparison : FixedObjectAugmentation.Map (initial A D) (initial A E) F where
  hom x y := (DGCategoryCycleCover.map A D E F).map x y
  map_id x := (DGCategoryCycleCover.map A D E F).map_id x
  map_comp x y z := (DGCategoryCycleCover.map A D E F).map_comp x y z
  augmentation x y := eq_of_heq
    (DGFunctor.hcongr_map (DGCategoryCycleCover.map_augmentation A D E F) x y)

end DGCategoryCellResolution
end SerrePositivity.DifferentialGraded
end

end InitialStageComparison

/-! ## FixedObjectMapAugmentation（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectMapAugmentation.lean） -/

/-! # cell付加後の比較と増大の可換性

## 概要
cell付加後の比較と増大の可換性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FixedObjectMapAugmentation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D] [Small.{u} D]
  {E : Type w} [dE : DGCategory A E] [Small.{u} E]
  {S : FixedObjectAugmentation A D D id} {T : FixedObjectAugmentation A E E id}
  {F : DGFunctor A D E} (M : Map S T F)
local notation "SA" => @FixedObjectAugmentation.attachedCategory A _ D D dD id S _
local notation "SD" => @FixedObjectAugmentation.category A _ D D dD id S
local notation "SI" => @FixedObjectAugmentation.CellIndex A _ D D dD id S
local notation "SC" => @FixedObjectAugmentation.cells A _ D D dD id S

def comparisonThenAugmentation : letI : DGCategory A D := S.category;
    DGFunctor A ((SC).Objects A D SI) E := by
  let obj := F.obj
  let m := M.attachedHom
  let t := T.attach.map
  have hi : ∀ x, S.attach.category.id x ≫ m x x = T.attach.category.id (obj x) :=
    M.attachedHom_id
  have hc : ∀ x y z, S.attach.category.comp x y z ≫ m x z =
    (m x y ⊗ₘ m y z) ≫ T.attach.category.comp (obj x) (obj y) (obj z) := M.attachedHom_comp
  have ti := T.attach.map_id
  have tc := T.attach.map_comp
  letI : DGCategory A D := S.category
  exact
    { obj := fun x => obj x.val
      map := fun x y => m x.val y.val ≫ t (obj x.val) (obj y.val)
      map_id := fun x => by
        change (SA).id x.val ≫ (m x.val x.val ≫ t (obj x.val) (obj x.val)) = _
        rw [← Category.assoc, hi, ti]
        rfl
      map_comp := fun x y z => by
        change (SA).comp x.val y.val z.val ≫ (m x.val z.val ≫ t (obj x.val) (obj z.val)) = _
        rw [← Category.assoc, hc, Category.assoc, tc,
          ← Category.assoc, ← tensorHom_comp_tensorHom]
        rfl }

def augmentationThenFunctor (_M : Map S T F) : letI : DGCategory A D := S.category;
    DGFunctor A ((SC).Objects A D SI) E := by
  let obj := F.obj
  let f := F.map
  let s := S.attach.map
  let origId := fun x : D => eId (Complex A) x
  let origComp := fun x y z : D => eComp (Complex A) x y z
  have si : ∀ x, (SA).id x ≫ s x x = origId x := S.attach.map_id
  have sc : ∀ x y z, (SA).comp x y z ≫ s x z =
    (s x y ⊗ₘ s y z) ≫ origComp x y z := S.attach.map_comp
  have fi : ∀ x, origId x ≫ f x x = eId (Complex A) (obj x) := F.map_id
  have fc : ∀ x y z, origComp x y z ≫ f x z =
    (f x y ⊗ₘ f y z) ≫ eComp (Complex A) (obj x) (obj y) (obj z) := F.map_comp
  letI : DGCategory A D := S.category
  exact
    { obj := fun x => obj x.val
      map := fun x y => s x.val y.val ≫ f x.val y.val
      map_id := fun x => by
        change (SA).id x.val ≫ (s x.val x.val ≫ f x.val x.val) = _
        rw [← Category.assoc, si, fi]
      map_comp := fun x y z => by
        change (SA).comp x.val y.val z.val ≫ (s x.val z.val ≫ f x.val z.val) = _
        rw [← Category.assoc, sc, Category.assoc, fc,
          ← Category.assoc, ← tensorHom_comp_tensorHom] }

lemma attachedFunctor_augmentation :
    comparisonThenAugmentation M = augmentationThenFunctor M := by
  have hm := M.transition_attachedHom
  have ht := T.transition_augmentation
  have hs := S.transition_augmentation
  have ha := M.augmentation
  have hg := M.attachedHom_cellGenerator
  have htg := T.attach_map_cellGenerator
  have hsg := S.attach_map_cellGenerator
  let L := comparisonThenAugmentation M
  let R := augmentationThenFunctor M
  let fm := F.map
  let obj := F.obj
  let sr := S.transition
  let sa := S.attach.map
  let ta := T.attach.map
  let am := M.attachedHom
  let gen := S.cellGenerator
  let tgen := T.cellGenerator
  let j := M.cellMap
  let : DGCategory A D := S.category
  apply (SC).functor_ext A D SI _
  · apply EnrichedFunctor.ext (Complex A)
      (F := (SC).restrictFunctor A D SI L) (G := (SC).restrictFunctor A D SI R) (fun _ => rfl)
    intro x y
    change ((_ ≫ (_ ≫ _)) ≫ eqToHom (by rfl)) = _
    rw [eqToHom_refl, Category.comp_id]
    change sr x y ≫ (am x y ≫ ta (obj x) (obj y)) =
      sr x y ≫ (sa x y ≫ fm x y)
    rw [← Category.assoc, hm, Category.assoc, ht, ha, ← Category.assoc, hs]
  · apply heq_of_eq
    funext i
    change (ta _ _).f i.2.2.degree ((am i.1 i.2.1).f i.2.2.degree (gen i)) =
      (fm i.1 i.2.1).f i.2.2.degree ((sa i.1 i.2.1).f i.2.2.degree (gen i))
    rw [hg]
    change (ta (j i).1 (j i).2.1).f (j i).2.2.degree (tgen (j i)) =
      (fm i.1 i.2.1).f i.2.2.degree ((sa i.1 i.2.1).f i.2.2.degree (gen i))
    rw [htg, hsg]
    rfl

lemma attachedHom_augmentation (x y : D) :
    M.attachedHom x y ≫ T.attach.map (F.obj x) (F.obj y) = S.attach.map x y ≫ F.map x y := by
  have h := M.attachedFunctor_augmentation
  let : DGCategory A D := S.category
  exact eq_of_heq (DGFunctor.hcongr_map h ⟨x⟩ ⟨y⟩)

/-- 増大比較を全境界cell付加の次段階へ延長する。 -/
def attach : Map S.attach T.attach F where
  hom := M.attachedHom
  map_id := M.attachedHom_id
  map_comp := M.attachedHom_comp
  augmentation := M.attachedHom_augmentation

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
end

end FixedObjectMapAugmentation

/-! ## FixedObjectMapLaws（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectMapLaws.lean） -/

/-!
概要：固定対象増大の比較の恒等・合成と、同じ境界 cell 添字の厳密移送。
方針：元の Hom 写像をそのまま合成し、指定 cycle と原始元を同時に送る。
規約：模型・対象ラベル・増大を変更しない。
使われ方：D-8 e の同じ cell 分解上の比較の厳密則。
-/

@[expose] public section FixedObjectMapLaws
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E] {B : Type z} [DGCategory A B]

lemma map_ext {S : FixedObjectAugmentation A D D id}
    {T : FixedObjectAugmentation A E E id} {F : DGFunctor A D E}
    {M N : Map S T F} (h : M.hom = N.hom) : M = N := by
  cases M
  cases N
  cases h
  rfl

def identity (S : FixedObjectAugmentation A D D id) : Map S S (DGFunctor.id D) where
  hom _ _ := 𝟙 _
  map_id _ := by rw [Category.comp_id]; rfl
  map_comp _ _ _ := by simp; rfl
  augmentation x y := by
    change 𝟙 _ ≫ S.map x y = S.map x y ≫ 𝟙 _
    simp

def composition {S : FixedObjectAugmentation A D D id}
    {T : FixedObjectAugmentation A E E id} {U : FixedObjectAugmentation A B B id}
    {F : DGFunctor A D E} {G : DGFunctor A E B} (M : Map S T F) (N : Map T U G) :
    Map S U (F.comp G) where
  hom x y := M.hom x y ≫ N.hom (F.obj x) (F.obj y)
  map_id x := by rw [← Category.assoc, M.map_id, N.map_id]; rfl
  map_comp x y z := by
    rw [← Category.assoc, M.map_comp, Category.assoc, N.map_comp,
      ← Category.assoc, ← tensorHom_comp_tensorHom]
    rfl
  augmentation x y := by
    change (M.hom x y ≫ N.hom (F.obj x) (F.obj y)) ≫
      U.map (G.obj (F.obj x)) (G.obj (F.obj y)) =
      S.map x y ≫ (F.map x y ≫ G.map (F.obj x) (F.obj y))
    rw [Category.assoc, N.augmentation, ← Category.assoc, M.augmentation, Category.assoc]

lemma identity_cellMap (S : FixedObjectAugmentation A D D id) (i : S.CellIndex) :
    (identity S).cellMap i = i := by
  rcases i with ⟨x, y, c⟩
  cases c
  rfl

lemma composition_cellMap {S : FixedObjectAugmentation A D D id}
    {T : FixedObjectAugmentation A E E id} {U : FixedObjectAugmentation A B B id}
    {F : DGFunctor A D E} {G : DGFunctor A E B} (M : Map S T F) (N : Map T U G)
    (i : S.CellIndex) : (composition M N).cellMap i = N.cellMap (M.cellMap i) := rfl

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
end

end FixedObjectMapLaws

/-! ## FixedObjectAttachmentExt（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectAttachmentExt.lean） -/

/-!
概要：同じ全境界 cell 付加上の増大比較を、元 Hom と新生成元で判定する。
方針：元の cell 付加の dg 関手普遍性を固定対象表示へ戻す。
規約：全次数 Hom の厳密等号であり、増大後の等号や導来等号ではない。
使われ方：D-8 e の固定分解作用の恒等・合成。
-/

@[expose] public section FixedObjectAttachmentExt
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D] [Small.{u} D]
  {E : Type w} [DGCategory A E]
  {S : FixedObjectAugmentation A D D id} {T : FixedObjectAugmentation A E E id}
  {F : DGFunctor A D E}
local notation "SI" => @FixedObjectAugmentation.CellIndex A _ D D dD id S
local notation "SC" => @FixedObjectAugmentation.cells A _ D D dD id S

def attachedSourceFunctor (M : Map S.attach T F) :
    letI : DGCategory A D := S.category; DGFunctor A ((SC).Objects A D SI) T.Objects := by
  let obj := F.obj
  let m := M.hom
  have hi := M.map_id
  have hc := M.map_comp
  letI : DGCategory A D := S.category
  exact
    { obj := fun x => ⟨obj x.val⟩
      map x y := m x.val y.val
      map_id x := hi x.val
      map_comp x y z := hc x.val y.val z.val }

lemma attached_hom_ext (M N : Map S.attach T F)
    (ht : ∀ x y, S.transition x y ≫ M.hom x y = S.transition x y ≫ N.hom x y)
    (hg : ∀ i : S.CellIndex,
      (M.hom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) =
        (N.hom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i)) (x y : D) :
    M.hom x y = N.hom x y := by
  have he : attachedSourceFunctor M = attachedSourceFunctor N := by
    let L := attachedSourceFunctor M
    let R := attachedSourceFunctor N
    let t := S.transition
    let m := M.hom
    let n := N.hom
    let : DGCategory A D := S.category
    apply (SC).functor_ext A D SI L R
    · apply EnrichedFunctor.ext (Complex A)
        (F := (SC).restrictFunctor A D SI L) (G := (SC).restrictFunctor A D SI R)
        (fun _ => rfl)
      intro a b
      change (t a b ≫ m a b) ≫ eqToHom (by rfl) = t a b ≫ n a b
      rw [eqToHom_refl, Category.comp_id]
      exact ht a b
    · apply heq_of_eq
      funext i
      exact hg i
  let : DGCategory A D := S.category
  exact eq_of_heq (DGFunctor.hcongr_map he ⟨x⟩ ⟨y⟩)

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
end

end FixedObjectAttachmentExt

/-! ## FixedObjectAttachmentLaws（旧 SerrePositivity/DifferentialGraded/Resolution/FixedObjectAttachmentLaws.lean） -/

/-!
概要：同じ全境界 cell 付加は増大比較の恒等・合成を厳密に保つ。
方針：元 Hom と指定境界 cell の生成元で全 Hom を判定する。
規約：増大の後での一致に弱めず、元の attachedHom 自体の等号を証明する。
使われ方：D-8 e の指定 cell 分解作用の段階帰納。
-/

@[expose] public section FixedObjectAttachmentLaws
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]

private lemma dependent_apply_heq {α : Sort*} {β : α → Sort*} (f : ∀ a, β a)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

lemma attach_identity (S : FixedObjectAugmentation A D D id) :
    (identity S).attach = identity S.attach := by
  apply map_ext
  funext x y
  apply attached_hom_ext
  · intro a b
    change S.transition a b ≫ (identity S).attachedHom a b = S.transition a b ≫ 𝟙 _
    rw [transition_attachedHom]
    change 𝟙 _ ≫ S.transition a b = S.transition a b ≫ 𝟙 _
    simp
  · intro i
    change ((identity S).attachedHom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) = _
    rw [attachedHom_cellGenerator]
    exact eq_of_heq (dependent_apply_heq S.cellGenerator (identity_cellMap S i))

variable {E : Type w} [DGCategory A E] [Small.{u} E]
  {B : Type z} [DGCategory A B] [Small.{u} B]

lemma attach_composition {S : FixedObjectAugmentation A D D id}
    {T : FixedObjectAugmentation A E E id} {U : FixedObjectAugmentation A B B id}
    {F : DGFunctor A D E} {G : DGFunctor A E B} (M : Map S T F) (N : Map T U G) :
    (composition M N).attach = composition M.attach N.attach := by
  apply map_ext
  funext x y
  apply attached_hom_ext
  · intro a b
    change S.transition a b ≫ (composition M N).attachedHom a b =
      S.transition a b ≫ (M.attachedHom a b ≫ N.attachedHom (F.obj a) (F.obj b))
    rw [transition_attachedHom, ← Category.assoc, transition_attachedHom,
      Category.assoc, transition_attachedHom]
    change (M.hom a b ≫ N.hom (F.obj a) (F.obj b)) ≫ _ = _
    rw [Category.assoc]
    rfl
  · intro i
    change ((composition M N).attachedHom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) =
      (N.attachedHom (F.obj i.1) (F.obj i.2.1)).f i.2.2.degree
        ((M.attachedHom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i))
    rw [attachedHom_cellGenerator, M.attachedHom_cellGenerator]
    have hn := N.attachedHom_cellGenerator (M.cellMap i)
    change (N.attachedHom (F.obj i.1) (F.obj i.2.1)).f i.2.2.degree
      (T.cellGenerator (M.cellMap i)) = U.cellGenerator (N.cellMap (M.cellMap i)) at hn
    rw [hn]
    exact eq_of_heq (dependent_apply_heq U.cellGenerator (composition_cellMap M N i))

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
end

end FixedObjectAttachmentLaws

/-! ## CellComparison（旧 SerrePositivity/DifferentialGraded/Resolution/CellComparison.lean） -/

/-! # dg関手に沿うcell反復列と最終解像度の比較

## 概要
dg関手に沿うcell反復列と最終解像度の比較。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CellComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def stageComparison : (n : ℕ) →
    FixedObjectAugmentation.Map (stage A D n) (stage A E n) F
  | 0 => initialComparison A D E F
  | n + 1 => (stageComparison n).attach

lemma transition_comparison (n : ℕ) (x y : D) :
    transition A D n x y ≫ (stageComparison A D E F (n + 1)).hom x y =
      (stageComparison A D E F n).hom x y ≫ transition A E n (F.obj x) (F.obj y) :=
  (stageComparison A D E F n).transition_attachedHom x y

def comparisonCocone (x y : D) : Cocone (homDiagram A D x y) where
  pt := candidateHom A E (F.obj x) (F.obj y)
  ι := NatTrans.ofSequence
    (fun n => (stageComparison A D E F n).hom x y ≫
      stageInclusion A E n (F.obj x) (F.obj y)) (fun n => by
      change (homDiagram A D x y).map (homOfLE (Nat.le_succ n)) ≫
        ((stageComparison A D E F (n + 1)).hom x y ≫
          stageInclusion A E (n + 1) (F.obj x) (F.obj y)) =
        ((stageComparison A D E F n).hom x y ≫
          stageInclusion A E n (F.obj x) (F.obj y)) ≫ 𝟙 _
      dsimp only [homDiagram]
      rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
      change transition A D n x y ≫
        ((stageComparison A D E F (n + 1)).hom x y ≫
          stageInclusion A E (n + 1) (F.obj x) (F.obj y)) = _
      rw [← Category.assoc, transition_comparison, Category.assoc, transition_inclusion])

def comparisonHom (x y : D) :
    candidateHom A D x y ⟶ candidateHom A E (F.obj x) (F.obj y) :=
  colimit.desc _ (comparisonCocone A D E F x y)

@[reassoc] lemma stageInclusion_comparison (n : ℕ) (x y : D) :
    stageInclusion A D n x y ≫ comparisonHom A D E F x y =
      (stageComparison A D E F n).hom x y ≫ stageInclusion A E n (F.obj x) (F.obj y) :=
  colimit.ι_desc _ _

lemma comparisonHom_augmentation (x y : D) :
    comparisonHom A D E F x y ≫ candidateAugmentation A E (F.obj x) (F.obj y) =
      candidateAugmentation A D x y ≫ F.map x y := by
  apply colimit.hom_ext
  intro n
  change stageInclusion A D n x y ≫ _ = stageInclusion A D n x y ≫ _
  rw [← Category.assoc, stageInclusion_comparison, Category.assoc,
    stageInclusion_augmentation, ← Category.assoc, stageInclusion_augmentation]
  exact (stageComparison A D E F n).augmentation x y

lemma comparisonHom_unit (x : D) :
    candidateUnit A D x ≫ comparisonHom A D E F x x = candidateUnit A E (F.obj x) := by
  rw [candidateUnit, Category.assoc, stageInclusion_comparison,
    ← Category.assoc, (stageComparison A D E F 0).map_id]
  rfl

lemma comparisonHom_comp (x y z : D) :
    candidateComposition A D x y z ≫ comparisonHom A D E F x z =
      (comparisonHom A D E F x y ⊗ₘ comparisonHom A D E F y z) ≫
        candidateComposition A E (F.obj x) (F.obj y) (F.obj z) := by
  apply (candidateTensorIsColimit A D x y z).hom_ext
  intro n
  change (stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ≫
    (candidateComposition A D x y z ≫ comparisonHom A D E F x z) =
    (stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ≫
      ((comparisonHom A D E F x y ⊗ₘ comparisonHom A D E F y z) ≫ _)
  rw [← Category.assoc, candidateComposition_stage, Category.assoc,
    stageInclusion_comparison, ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom,
    stageInclusion_comparison, stageInclusion_comparison, ← tensorHom_comp_tensorHom,
    (stageComparison A D E F n).map_comp]
  simp only [Category.assoc]
  rw [candidateComposition_stage]

/-- 最終増大の厳密な可換squareを伴う比較。 -/
def comparison : FixedObjectAugmentation.Map (candidate A D) (candidate A E) F where
  hom := comparisonHom A D E F
  map_id := comparisonHom_unit A D E F
  map_comp := comparisonHom_comp A D E F
  augmentation := comparisonHom_augmentation A D E F

def comparisonFunctor : DGFunctor A (Source A D) (Source A E) :=
  (comparison A D E F).toDGFunctor

lemma comparisonFunctor_augmentation :
    (comparisonFunctor A D E F).comp (augmentation A E) = (augmentation A D).comp F := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (comparisonFunctor A D E F).comp (augmentation A E))
    (G := (augmentation A D).comp F) (fun _ => rfl)
  intro x y
  change (comparisonHom A D E F x.val y.val ≫
    candidateAugmentation A E (F.obj x.val) (F.obj y.val)) ≫ eqToHom (by rfl) = _
  rw [eqToHom_refl, Category.comp_id, comparisonHom_augmentation]
  rfl

lemma comparisonHom_quasiIso (hF : HomQuasiIso F) (x y : D) :
    QuasiIso (comparisonHom A D E F x y) := by
  let : QuasiIso (F.map x y) := hF x y
  let : QuasiIso (candidateAugmentation A D x y) :=
    candidateAugmentation_quasiIso A D x y
  let : QuasiIso (candidateAugmentation A E (F.obj x) (F.obj y)) :=
    candidateAugmentation_quasiIso A E (F.obj x) (F.obj y)
  have : QuasiIso (comparisonHom A D E F x y ≫
      candidateAugmentation A E (F.obj x) (F.obj y)) := by
    rw [comparisonHom_augmentation]
    infer_instance
  exact quasiIso_of_comp_right _ (candidateAugmentation A E (F.obj x) (F.obj y))

lemma comparisonFunctor_homQuasiIso (hF : HomQuasiIso F) :
    HomQuasiIso (comparisonFunctor A D E F) :=
  fun x y => comparisonHom_quasiIso A D E F hF x.val y.val

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
end

end CellComparison

/-! ## CellComparisonLaws（旧 SerrePositivity/DifferentialGraded/Resolution/CellComparisonLaws.lean） -/

/-!
概要：元の標準 cell 解像度の比較関手は恒等・合成を厳密に保つ。
方針：同じ初期被覆と境界 cell 付加の厳密則を全段階へ帰納し、実余極限で判定する。
規約：通常 dg 射の全 Hom に関する等号。全 native Hom への作用は別工程。
使われ方：D-8 e の同じ分解 cone・実核・懸垂への射作用。
-/

@[expose] public section CellComparisonLaws
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma initialComparison_identity :
    initialComparison A D D (DGFunctor.id D) =
      FixedObjectAugmentation.Map.identity (initial A D) := by
  apply FixedObjectAugmentation.Map.map_ext
  funext x y
  exact eq_of_heq (DGFunctor.hcongr_map (DGCategoryCycleCover.map_identity A D) x y)

lemma stageComparison_identity (n : ℕ) :
    stageComparison A D D (DGFunctor.id D) n =
      FixedObjectAugmentation.Map.identity (stage A D n) := by
  induction n with
  | zero => exact initialComparison_identity A D
  | succ n ih =>
    change (stageComparison A D D (DGFunctor.id D) n).attach = _
    rw [ih, FixedObjectAugmentation.Map.attach_identity]
    rfl

lemma comparisonHom_identity (x y : D) :
    comparisonHom A D D (DGFunctor.id D) x y = 𝟙 (candidateHom A D x y) := by
  apply colimit.hom_ext
  intro n
  change stageInclusion A D n x y ≫ comparisonHom A D D (DGFunctor.id D) x y =
    stageInclusion A D n x y ≫ 𝟙 _
  rw [stageInclusion_comparison]
  have h : (stageComparison A D D (DGFunctor.id D) n).hom x y = 𝟙 _ :=
    congrArg (fun M => M.hom x y) (stageComparison_identity A D n)
  rw [h]
  change 𝟙 _ ≫ stageInclusion A D n x y = stageInclusion A D n x y ≫ 𝟙 _
  simp

lemma comparisonFunctor_identity :
    comparisonFunctor A D D (DGFunctor.id D) = DGFunctor.id (Source A D) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := comparisonFunctor A D D (DGFunctor.id D)) (G := DGFunctor.id (Source A D))
    (fun _ => rfl)
  intro x y
  change comparisonHom A D D (DGFunctor.id D) x.val y.val ≫ eqToHom (by rfl) = 𝟙 _
  rw [eqToHom_refl, Category.comp_id, comparisonHom_identity]

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]

lemma initialComparison_composition (F : DGFunctor A D E) (G : DGFunctor A E B) :
    initialComparison A D B (F.comp G) = FixedObjectAugmentation.Map.composition
      (initialComparison A D E F) (initialComparison A E B G) := by
  apply FixedObjectAugmentation.Map.map_ext
  funext x y
  exact eq_of_heq (DGFunctor.hcongr_map (DGCategoryCycleCover.map_composition A D E B F G) x y)

lemma stageComparison_composition (F : DGFunctor A D E) (G : DGFunctor A E B) (n : ℕ) :
    stageComparison A D B (F.comp G) n = FixedObjectAugmentation.Map.composition
      (stageComparison A D E F n) (stageComparison A E B G n) := by
  induction n with
  | zero => exact initialComparison_composition A D E B F G
  | succ n ih =>
    change (stageComparison A D B (F.comp G) n).attach =
      FixedObjectAugmentation.Map.composition
        (stageComparison A D E F n).attach (stageComparison A E B G n).attach
    rw [ih, FixedObjectAugmentation.Map.attach_composition]

lemma comparisonHom_composition (F : DGFunctor A D E) (G : DGFunctor A E B) (x y : D) :
    comparisonHom A D B (F.comp G) x y =
      comparisonHom A D E F x y ≫ comparisonHom A E B G (F.obj x) (F.obj y) := by
  apply colimit.hom_ext
  intro n
  change stageInclusion A D n x y ≫ comparisonHom A D B (F.comp G) x y =
    stageInclusion A D n x y ≫ (comparisonHom A D E F x y ≫
      comparisonHom A E B G (F.obj x) (F.obj y))
  rw [stageInclusion_comparison, ← Category.assoc, stageInclusion_comparison,
    Category.assoc, stageInclusion_comparison]
  have h : (stageComparison A D B (F.comp G) n).hom x y =
      (stageComparison A D E F n).hom x y ≫
        (stageComparison A E B G n).hom (F.obj x) (F.obj y) :=
    congrArg (fun M => M.hom x y) (stageComparison_composition A D E B F G n)
  rw [h, Category.assoc]
  rfl

lemma comparisonFunctor_composition (F : DGFunctor A D E) (G : DGFunctor A E B) :
    comparisonFunctor A D B (F.comp G) =
      (comparisonFunctor A D E F).comp (comparisonFunctor A E B G) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := comparisonFunctor A D B (F.comp G))
    (G := (comparisonFunctor A D E F).comp (comparisonFunctor A E B G)) (fun _ => rfl)
  intro x y
  change comparisonHom A D B (F.comp G) x.val y.val ≫ eqToHom (by rfl) =
    comparisonHom A D E F x.val y.val ≫ comparisonHom A E B G (F.obj x.val) (F.obj y.val)
  rw [eqToHom_refl, Category.comp_id, comparisonHom_composition]

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
end

end CellComparisonLaws

/-! ## CellComparisonQuasiEquivalence（旧 SerrePositivity/DifferentialGraded/Resolution/CellComparisonQuasiEquivalence.lean） -/

/-! # 準同値に沿う標準解像度の準同値比較

## 概要
準同値に沿う標準解像度の準同値比較。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CellComparisonQuasiEquivalence
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma comparisonFunctor_essSurj (hF : F.onHomotopy.EssSurj) :
    (comparisonFunctor A D E F).onHomotopy.EssSurj := by
  let : (augmentation A D).onHomotopy.EssSurj := augmentation_essSurj A D
  let : F.onHomotopy.EssSurj := hF
  let : (augmentation A E).onHomotopy.Full :=
    (augmentation A E).onHomotopy_full_of_homQuasiIso (augmentation_homQuasiIso A E)
  let : (augmentation A E).onHomotopy.Faithful :=
    (augmentation A E).onHomotopy_faithful_of_homQuasiIso (augmentation_homQuasiIso A E)
  have hs : (comparisonFunctor A D E F).onHomotopy ⋙ (augmentation A E).onHomotopy =
      (augmentation A D).onHomotopy ⋙ F.onHomotopy := by
    rw [← DGFunctor.onHomotopy_comp, comparisonFunctor_augmentation, DGFunctor.onHomotopy_comp]
  have : ((comparisonFunctor A D E F).onHomotopy ⋙
      (augmentation A E).onHomotopy).EssSurj := by
    rw [hs]
    infer_instance
  exact Functor.essSurj_of_comp_fully_faithful _ (augmentation A E).onHomotopy

lemma comparisonFunctor_quasiEquivalence (hF : QuasiEquivalence F) :
    QuasiEquivalence (comparisonFunctor A D E F) :=
  ⟨comparisonFunctor_homQuasiIso A D E F hF.1, comparisonFunctor_essSurj A D E F hF.2⟩

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
end

end CellComparisonQuasiEquivalence

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Drinfeld "Construction §3.5"] _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.resolution
