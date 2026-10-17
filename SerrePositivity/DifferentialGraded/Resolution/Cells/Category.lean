module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Associativity
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # 指定境界を持つ任意次数cell付加の主豊穣dg圏

対象を元のdg圏と区別して、Homの追加微分を持つ別の豊穣構造を登録する。
cell生成元の境界式・増大・K-flat filtrationは後続で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]

/-- cell族と結び付けた対象型。元のDの豊穣instanceは変更しない。 -/
structure Objects (_C : Family A D I) where
  val : D

variable (C : Family A D I)

def objectEquiv : D ≃ C.Objects A D I where
  toFun x := ⟨x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl

instance objectsSmall [Small.{u} D] : Small.{u} (C.Objects A D I) :=
  small_of_injective (f := fun x : C.Objects A D I => x.val) (by
    rintro ⟨x⟩ ⟨y⟩ h
    cases h
    rfl)

/-- 追加微分後のHom・閉単位・合成と三つの圏法則によるMathlib豊穣構造。 -/
instance attachedDGCategory : DGCategory A (C.Objects A D I) :=
  ofHomObjects A (C.Objects A D I)
    (fun x y => C.attachedHom A D I x.val y.val)
    (fun x => C.attachedIdentity A D I x.val)
    (fun x y z => C.attachedComposition A D I x.val y.val z.val)
    (fun x y => C.attachedComposition_left_unit A D I x.val y.val)
    (fun x y => C.attachedComposition_right_unit A D I x.val y.val)
    (fun a b c d => by rw [attachedComposition_assoc, Iso.inv_hom_id_assoc])

/-- 元のHomを空pathへ入れるdg関手。 -/
def embedding : DGFunctor A D (C.Objects A D I) where
  obj x := ⟨x⟩
  map x y := C.originalHomInclusion A D I x y
  map_id _x := rfl
  map_comp x y z := (C.attachedComposition_original A D I x y z).symm

/-- 豊穣順合成と通常順dg合成のKoszul符号の一致。 -/
lemma attachedComposition_eq_signed_compose (x y z : D) (p q n : ℤ) (hn : p + q = n)
    (f : (C.attachedHom A D I x y).X p) (g : (C.attachedHom A D I y z).X q) :
    (C.attachedComposition A D I x y z).f n
      (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (f ⊗ₜ[A] g)) =
    (p * q).negOnePow • compose A (x := (⟨x⟩ : C.Objects A D I))
      (y := (⟨y⟩ : C.Objects A D I)) (z := (⟨z⟩ : C.Objects A D I)) g f hn :=
  forward_eq_signed_compose A (D := C.Objects A D I)
    (x := ⟨x⟩) (y := ⟨y⟩) (z := ⟨z⟩) f g hn

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
