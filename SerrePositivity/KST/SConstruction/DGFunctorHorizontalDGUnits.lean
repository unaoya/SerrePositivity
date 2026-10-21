module
public import SerrePositivity.KST.SConstruction.DGFunctorIdentityPoint
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalDG
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalOuterUnit
public import SerrePositivity.KST.SConstruction.DGTensorFunctor
public import SerrePositivity.KST.SConstruction.DGTensorUnitors

/-! # 元の tensor dg 横合成関手の左右単位等号
概要：元の恒等関手を一対象 A から挿入する横合成を、実 dg tensor 単位関手と比較する。
方針：元の Hom 移送付き左右単位則から、monoidal 単位逆射を消去する。
規約：元の閉単位と対象等号を保持。使われ方：native 直積横合成の単位則。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D]

/-- 元の恒等 dg 関手を左から挿入して、元の全次数横合成を適用する実 dg 関手。 -/
def dgFunctorHorizontalLeftUnitDG :
    DGFunctor A (DGTensorCategory A PUnit.{1} (DGFunctor A D E)) (DGFunctor A D E) :=
  DGFunctor.comp
    (dgTensorFunctor A (dgFunctorIdentityPoint A D) (DGFunctor.id (DGFunctor A D E)))
    (dgFunctorHorizontalDG A D D E)

/-- 元の恒等 dg 関手の左挿入の全 Hom は、閉単位と元の横合成そのもの。 -/
lemma dgFunctorHorizontalLeftUnitDG_map
    (x y : DGTensorCategory A PUnit.{1} (DGFunctor A D E)) :
    (dgFunctorHorizontalLeftUnitDG A D E).map x y =
      (dgFunctorIdentity A D D (DGFunctor.id D) ⊗ₘ 𝟙 (dgFunctorHom A D E x.2 y.2)) ≫
        dgFunctorHorizontal A D D E (DGFunctor.id D) (DGFunctor.id D) x.2 y.2 := rfl

/-- 元の恒等 dg 関手による左横合成は、元の実 dg tensor 左単位関手に等しい。 -/
lemma dgFunctorHorizontalDG_left_unit :
    dgFunctorHorizontalLeftUnitDG A D E = dgTensorLeftUnitor A (DGFunctor A D E) := by
  refine EnrichedFunctor.ext (Complex A)
    (F := dgFunctorHorizontalLeftUnitDG A D E)
    (G := dgTensorLeftUnitor A (DGFunctor A D E))
    (fun x => strictDGFunctor_id_comp x.2) ?_
  intro x y
  rw [dgFunctorHorizontalLeftUnitDG_map, dgTensorLeftUnitor_map]
  change ((dgFunctorIdentity A D D (DGFunctor.id D) ⊗ₘ
      𝟙 (dgFunctorHom A D E x.2 y.2)) ≫
      dgFunctorHorizontal A D D E (DGFunctor.id D) (DGFunctor.id D) x.2 y.2) ≫
      dgFunctorHomTransport A D E (strictDGFunctor_id_comp x.2) (strictDGFunctor_id_comp y.2) =
    (λ_ (dgFunctorHom A D E x.2 y.2)).hom
  apply (cancel_epi (λ_ (dgFunctorHom A D E x.2 y.2)).inv).mp
  simpa only [tensorHom_id, Category.assoc, Iso.inv_hom_id] using
    dgFunctorHorizontal_left_unit A D E x.2 y.2

variable [Small.{u} E]

/-- 元の恒等 dg 関手を右から挿入して、元の全次数横合成を適用する実 dg 関手。 -/
def dgFunctorHorizontalRightUnitDG :
    DGFunctor A (DGTensorCategory A (DGFunctor A D E) PUnit.{1}) (DGFunctor A D E) :=
  DGFunctor.comp
    (dgTensorFunctor A (DGFunctor.id (DGFunctor A D E)) (dgFunctorIdentityPoint A E))
    (dgFunctorHorizontalDG A D E E)

/-- 元の恒等 dg 関手の右挿入の全 Hom は、元の横合成と閉単位そのもの。 -/
lemma dgFunctorHorizontalRightUnitDG_map
    (x y : DGTensorCategory A (DGFunctor A D E) PUnit.{1}) :
    (dgFunctorHorizontalRightUnitDG A D E).map x y =
      (𝟙 (dgFunctorHom A D E x.1 y.1) ⊗ₘ dgFunctorIdentity A E E (DGFunctor.id E)) ≫
        dgFunctorHorizontal A D E E x.1 y.1 (DGFunctor.id E) (DGFunctor.id E) := rfl

/-- 元の恒等 dg 関手による右横合成は、元の実 dg tensor 右単位関手に等しい。 -/
lemma dgFunctorHorizontalDG_right_unit :
    dgFunctorHorizontalRightUnitDG A D E = dgTensorRightUnitor A (DGFunctor A D E) := by
  refine EnrichedFunctor.ext (Complex A)
    (F := dgFunctorHorizontalRightUnitDG A D E)
    (G := dgTensorRightUnitor A (DGFunctor A D E))
    (fun x => strictDGFunctor_comp_id x.1) ?_
  intro x y
  rw [dgFunctorHorizontalRightUnitDG_map, dgTensorRightUnitor_map]
  change ((𝟙 (dgFunctorHom A D E x.1 y.1) ⊗ₘ
      dgFunctorIdentity A E E (DGFunctor.id E)) ≫
      dgFunctorHorizontal A D E E x.1 y.1 (DGFunctor.id E) (DGFunctor.id E)) ≫
      dgFunctorHomTransport A D E (strictDGFunctor_comp_id x.1) (strictDGFunctor_comp_id y.1) =
    (ρ_ (dgFunctorHom A D E x.1 y.1)).hom
  apply (cancel_epi (ρ_ (dgFunctorHom A D E x.1 y.1)).inv).mp
  simpa only [id_tensorHom, Category.assoc, Iso.inv_hom_id] using
    dgFunctorHorizontal_right_unit A D E x.1 y.1

end SerrePositivity.KST.SConstruction
