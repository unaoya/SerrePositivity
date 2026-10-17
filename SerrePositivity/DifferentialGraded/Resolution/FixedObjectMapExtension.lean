module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectMap
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Universal

/-! # 増大比較のcell付加後への延長

## 概要
増大比較のcell付加後への延長。

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
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D] [Small.{u} D]
  {E : Type w} [dE : DGCategory A E] [Small.{u} E]
  {S : FixedObjectAugmentation A D D id} {T : FixedObjectAugmentation A E E id}
  {F : DGFunctor A D E} (M : Map S T F)

local notation "SD" => @FixedObjectAugmentation.category A _ D D dD id S
local notation "TD" => @FixedObjectAugmentation.category A _ E E dE id T
local notation "SI" => @FixedObjectAugmentation.CellIndex A _ D D dD id S
local notation "TI" => @FixedObjectAugmentation.CellIndex A _ E E dE id T
local notation "SC" => @FixedObjectAugmentation.cells A _ D D dD id S
local notation "TC" => @FixedObjectAugmentation.cells A _ E E dE id T

def baseExtension : letI : DGCategory A D := S.category;
    letI : DGCategory A E := T.category; DGFunctor A D ((TC).Objects A E TI) := by
  let obj := F.obj
  let m := M.hom
  let t := T.transition
  have hi : ∀ x, (SD).id x ≫ m x x = (TD).id (obj x) := M.map_id
  have hc : ∀ x y z, (SD).comp x y z ≫ m x z =
    (m x y ⊗ₘ m y z) ≫ (TD).comp (obj x) (obj y) (obj z) := M.map_comp
  have ht : ∀ x y z, (TD).comp x y z ≫ t x z =
    (t x y ⊗ₘ t y z) ≫ T.attach.category.comp x y z := T.transition_comp
  letI : DGCategory A D := S.category
  letI : DGCategory A E := T.category
  exact
    { obj := fun x => ⟨obj x⟩
      map := fun x y => m x y ≫ t (obj x) (obj y)
      map_id := fun x => by
        change (SD).id x ≫ (m x x ≫ t (obj x) (obj x)) =
          (TD).id (obj x) ≫ t (obj x) (obj x)
        rw [← Category.assoc, hi]
      map_comp := fun x y z => by
        change (SD).comp x y z ≫ (m x z ≫ t (obj x) (obj z)) = _
        rw [← Category.assoc, hc, Category.assoc, ht,
          ← Category.assoc, ← tensorHom_comp_tensorHom]
        rfl }

def extensionPrimitives : letI : DGCategory A D := S.category;
    letI : DGCategory A E := T.category;
    DGCellAttachment.Family.PrimitiveData A D SI SC
      ((TC).Objects A E TI) (baseExtension (dD := dD) (dE := dE) M) := by
  letI : DGCategory A D := S.category
  letI : DGCategory A E := T.category
  exact
    { primitive := fun i => (TC).generatorElement A E TI (cellMap (dD := dD) (dE := dE) M i)
      boundary := fun i => (TC).differential_generatorElement A E TI
        (cellMap (dD := dD) (dE := dE) M i) }

def attachedFunctor : letI : DGCategory A D := S.category;
    letI : DGCategory A E := T.category;
    DGFunctor A ((SC).Objects A D SI) ((TC).Objects A E TI) := by
  letI : DGCategory A D := S.category
  letI : DGCategory A E := T.category
  exact (extensionPrimitives (dD := dD) (dE := dE) M).extension

/-- 延長後のHom写像。対象写像は元のdg関手Fのまま。 -/
def attachedHom (x y : D) :
    S.attach.category.Hom x y ⟶ T.attach.category.Hom (F.obj x) (F.obj y) := by
  letI : DGCategory A D := S.category
  letI : DGCategory A E := T.category
  exact (attachedFunctor (dD := dD) (dE := dE) M).map ⟨x⟩ ⟨y⟩

lemma transition_attachedHom (x y : D) :
    S.transition x y ≫ M.attachedHom x y =
      M.hom x y ≫ T.transition (F.obj x) (F.obj y) := by
  let : DGCategory A D := S.category
  let : DGCategory A E := T.category
  exact (extensionPrimitives (dD := dD) (dE := dE) M).attachedEvaluation_original x y

lemma attachedHom_id (x : D) :
    S.attach.category.id x ≫ M.attachedHom x x = T.attach.category.id (F.obj x) := by
  let : DGCategory A D := S.category
  let : DGCategory A E := T.category
  exact (attachedFunctor (dD := dD) (dE := dE) M).map_id ⟨x⟩

lemma attachedHom_comp (x y z : D) :
    S.attach.category.comp x y z ≫ M.attachedHom x z =
      (M.attachedHom x y ⊗ₘ M.attachedHom y z) ≫
        T.attach.category.comp (F.obj x) (F.obj y) (F.obj z) := by
  let : DGCategory A D := S.category
  let : DGCategory A E := T.category
  exact (attachedFunctor (dD := dD) (dE := dE) M).map_comp ⟨x⟩ ⟨y⟩ ⟨z⟩

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
