module
public import SerrePositivity.DifferentialGraded.Resolution.CellSequence
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Filtered.Final

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
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
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
