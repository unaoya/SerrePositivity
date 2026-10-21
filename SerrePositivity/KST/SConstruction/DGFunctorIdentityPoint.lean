module
public import SerrePositivity.KST.SConstruction.DGFunctorEnrichment
public import SerrePositivity.DifferentialGraded.Category.Examples

/-! # 恒等 dg 関手を選ぶ一対象 A からの実 dg 関手
概要：入力圏の恒等 dg 関手と元の Hom end の閉単位を、一対象 A からの関手にする。
方針：全次数 dg 関手圏の元の単位則と monoidal 左単位の自然性を使う。
規約：対象と閉単位の選択は元の恒等に固定。使われ方：native 横合成の単位。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の恒等 dg 関手と全 Hom end の閉単位を選ぶ、一対象 A からの実 dg 関手。 -/
def dgFunctorIdentityPoint : DGFunctor A PUnit.{1} (DGFunctor A D D) where
  obj _ := DGFunctor.id D
  map _ _ := eId (Complex A) (DGFunctor.id (A := A) D)
  map_id _ := Category.id_comp _
  map_comp _ _ _ := by
    let F := DGFunctor.id (A := A) D
    have h : (eId (Complex A) F ▷ (F ⟶[Complex A] F)) ≫ eComp (Complex A) F F F =
        (λ_ (F ⟶[Complex A] F)).hom := by
      apply (cancel_epi (λ_ (F ⟶[Complex A] F)).inv).mp
      rw [e_id_comp, Iso.inv_hom_id]
    change (λ_ (𝟙_ (Complex A))).hom ≫ eId (Complex A) F =
      (eId (Complex A) F ⊗ₘ eId (Complex A) F) ≫ eComp (Complex A) F F F
    rw [tensorHom_def', Category.assoc, h, leftUnitor_naturality]

/-- 一対象 A からの元の単位選択は、元の恒等 dg 関手を対象として回収する。 -/
lemma dgFunctorIdentityPoint_obj (x : PUnit.{1}) :
    (dgFunctorIdentityPoint A D).obj x = DGFunctor.id D := rfl

/-- 一対象 A からの元の単位選択は、全 Hom end の元の閉単位を回収する。 -/
lemma dgFunctorIdentityPoint_map (x y : PUnit.{1}) :
    (dgFunctorIdentityPoint A D).map x y = dgFunctorIdentity A D D (DGFunctor.id D) := rfl

end SerrePositivity.KST.SConstruction
