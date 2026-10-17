module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectAugmentation
public import SerrePositivity.DifferentialGraded.Resolution.BoundarySequence
public import Mathlib.CategoryTheory.Functor.OfSequence

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
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
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
