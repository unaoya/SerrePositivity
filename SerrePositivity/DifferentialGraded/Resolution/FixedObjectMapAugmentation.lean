module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectGenerators
public import SerrePositivity.DifferentialGraded.Resolution.InitialStageComparison

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
