module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectAugmentation

/-! # 固定対象の豊穣構造を独立した対象型上の主dg圏へ戻す -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation
open CategoryTheory
variable {A : Type u} [CommRing A] {X : Type v} {E : Type w} [DGCategory A E] {o : X → E}

structure Objects (_S : FixedObjectAugmentation A X E o) where
  val : X

variable (S : FixedObjectAugmentation A X E o)

def objectEquiv : X ≃ S.Objects where
  toFun x := ⟨x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl

instance objectsSmall [Small.{u} X] : Small.{u} S.Objects :=
  small_of_injective (f := fun x : S.Objects => x.val) (by
    rintro ⟨x⟩ ⟨y⟩ h
    cases h
    rfl)

instance objectsDGCategory : DGCategory A S.Objects :=
  ofHomObjects A S.Objects (fun x y => S.category.Hom x.val y.val)
    (fun x => S.category.id x.val) (fun x y z => S.category.comp x.val y.val z.val)
    (fun x y => S.category.id_comp x.val y.val)
    (fun x y => S.category.comp_id x.val y.val)
    (fun w x y z => S.category.assoc w.val x.val y.val z.val)

def augmentation : DGFunctor A S.Objects E where
  obj x := o x.val
  map x y := S.map x.val y.val
  map_id x := S.map_id x.val
  map_comp x y z := S.map_comp x.val y.val z.val

lemma objects_homKFlat (hS : S.HomKFlat) : localHomKFlat A S.Objects :=
  fun x y => hS x.val y.val

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation
