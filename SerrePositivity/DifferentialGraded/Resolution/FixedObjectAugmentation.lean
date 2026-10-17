module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Augmentation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.LengthColimit

/-! # 対象ラベルと増大の対象写像を固定した豊穣構造

## 概要
反復列でMathlibのEnrichedCategoryをデータとして保持する。
対象Xの既存instanceを書き換えず、増大の対象写像oを全段階で固定する。

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
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (X : Type v) (E : Type w) [DGCategory A E] (o : X → E)

structure FixedObjectAugmentation where
  category : DGCategory A X
  map (x y : X) : category.Hom x y ⟶ homObject A E (o x) (o y)
  map_id (x : X) : category.id x ≫ map x x = eId (Complex A) (o x)
  map_comp (x y z : X) : category.comp x y z ≫ map x z =
    (map x y ⊗ₘ map y z) ≫ eComp (Complex A) (o x) (o y) (o z)

namespace FixedObjectAugmentation
variable {A X E o} (S : FixedObjectAugmentation A X E o)

def toDGFunctor : letI : DGCategory A X := S.category; DGFunctor A X E := by
  letI : DGCategory A X := S.category
  exact
    { obj := o
      map := S.map
      map_id := S.map_id
      map_comp := S.map_comp }

abbrev CellIndex := Σ x : X, Σ y : X, ComplexBoundaryCell A (S.map x y)

instance cellIndexSmall [Small.{u} X] : Small.{u} S.CellIndex := inferInstance

def cells : letI : DGCategory A X := S.category; DGCellAttachment.Family A X S.CellIndex := by
  letI : DGCategory A X := S.category
  exact
    { source := fun i => i.1
      target := fun i => i.2.1
      degree := fun i => i.2.2.degree
      boundary := fun i => i.2.2.cycle }

def cellPrimitives : letI : DGCategory A X := S.category;
    DGCellAttachment.Family.PrimitiveData A X S.CellIndex S.cells E S.toDGFunctor := by
  letI : DGCategory A X := S.category
  exact
    { primitive := fun i => i.2.2.primitive
      boundary := fun i => i.2.2.boundary }

variable [Small.{u} X]

@[instance_reducible]
def attachedCategory : DGCategory A X := by
  letI : DGCategory A X := S.category
  exact ofHomObjects A X
    (S.cells.attachedHom A X S.CellIndex)
    (S.cells.attachedIdentity A X S.CellIndex)
    (S.cells.attachedComposition A X S.CellIndex)
    (S.cells.attachedComposition_left_unit A X S.CellIndex)
    (S.cells.attachedComposition_right_unit A X S.CellIndex)
    (fun a b c d => by
      rw [DGCellAttachment.Family.attachedComposition_assoc, Iso.inv_hom_id_assoc])

/-- 全境界cellを付加しても、対象ラベルXと写像oを変えない。 -/
def attach : FixedObjectAugmentation A X E o := by
  letI : DGCategory A X := S.category
  exact
    { category := S.attachedCategory
      map := S.cellPrimitives.attachedEvaluation
      map_id := S.cellPrimitives.attachedEvaluation_unit
      map_comp := S.cellPrimitives.attachedEvaluation_composition }

def transition (x y : X) : S.category.Hom x y ⟶ S.attach.category.Hom x y := by
  letI : DGCategory A X := S.category
  exact S.cells.originalHomInclusion A X S.CellIndex x y

lemma transition_id (x : X) : S.category.id x ≫ S.transition x x = S.attach.category.id x := rfl

lemma transition_comp (x y z : X) :
    S.category.comp x y z ≫ S.transition x z =
    (S.transition x y ⊗ₘ S.transition y z) ≫ S.attach.category.comp x y z := by
  let : DGCategory A X := S.category
  exact (S.cells.attachedComposition_original A X S.CellIndex x y z).symm

lemma transition_augmentation (x y : X) : S.transition x y ≫ S.attach.map x y = S.map x y := by
  let : DGCategory A X := S.category
  exact S.cellPrimitives.attachedEvaluation_original x y

lemma attach_fills (x y : X) (c : ComplexBoundaryCell A (S.map x y)) :
    ∃ t : (S.attach.category.Hom x y).X c.degree,
      (S.attach.category.Hom x y).d c.degree (c.degree + 1) t =
        (S.transition x y).f (c.degree + 1) c.cycle.val ∧
      (S.attach.map x y).f c.degree t = c.primitive := by
  let : DGCategory A X := S.category
  let i : S.CellIndex := ⟨x, y, c⟩
  refine ⟨S.cells.generatorElement A X S.CellIndex i, ?_, ?_⟩
  · exact S.cells.differential_generatorElement A X S.CellIndex i
  · exact S.cellPrimitives.attachedEvaluation_generator i

def HomKFlat : Prop := ∀ x y : X, complexKFlat A (S.category.Hom x y)

lemma attach_homKFlat (hS : S.HomKFlat) : S.attach.HomKFlat := by
  let : DGCategory A X := S.category
  intro x y
  exact S.cells.attachedHom_kFlat A X S.CellIndex hS x y

end FixedObjectAugmentation
end SerrePositivity.DifferentialGraded
