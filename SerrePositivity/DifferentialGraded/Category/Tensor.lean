module
public import SerrePositivity.DifferentialGraded.Module.Basic

/-! # 二つのdg圏のtensor積

Homの組の豊穣を、Mathlibのtensorモノイダル関手でtransportする。
合成の交差は同関手のtensorμであり、独自の圏構造を増やさない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]

/-- 同じHom宇宙の複体の積に、既存の積monoidal構造を指定する。 -/
instance complexPairMonoidal : MonoidalCategory (Complex A × Complex A) :=
  MonoidalCategory.prodMonoidal (Complex A) (Complex A)

/-- Homを組として保持する積基底上の豊穣構造。 -/
instance dgPairEnrichment : EnrichedCategory (Complex A × Complex A) (B × C) where
  Hom x y := (x.1 ⟶[Complex A] y.1, x.2 ⟶[Complex A] y.2)
  id x := ⟨eId (Complex A) x.1, eId (Complex A) x.2⟩
  comp x y z := ⟨eComp (Complex A) x.1 y.1 z.1, eComp (Complex A) x.2 y.2 z.2⟩
  id_comp x y := Prod.ext (e_id_comp (Complex A) x.1 y.1) (e_id_comp (Complex A) x.2 y.2)
  comp_id x y := Prod.ext (e_comp_id (Complex A) x.1 y.1) (e_comp_id (Complex A) x.2 y.2)
  assoc x y z t := Prod.ext (e_assoc (Complex A) x.1 y.1 z.1 t.1)
    (e_assoc (Complex A) x.2 y.2 z.2 t.2)

/-- dg圏のtensor積。対象は組、HomはHom複体のtensor積。 -/
abbrev DGTensorCategory := TransportEnrichment (tensor (Complex A)) (B × C)

@[instance_reducible]
def dgTensorEnrichment : DGCategory A (DGTensorCategory A B C) := inferInstance

lemma dgTensor_hom (x y : DGTensorCategory A B C) :
    (x ⟶[Complex A] y) = (x.1 ⟶[Complex A] y.1) ⊗ (x.2 ⟶[Complex A] y.2) := rfl

/-- tensor積の単位は二つの閉単位のtensorから得る。 -/
lemma dgTensor_identity (x : DGTensorCategory A B C) :
    eId (Complex A) x = (λ_ (𝟙_ (Complex A))).inv ≫
      (eId (Complex A) x.1 ⊗ₘ eId (Complex A) x.2) := by
  rw [TransportEnrichment.eId_eq, tensor_ε]
  rfl

/-- 豊穣合成では中央二因子のsigned braidingを使う。 -/
lemma dgTensor_composition (x y z : DGTensorCategory A B C) :
    eComp (Complex A) x y z =
      tensorμ (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2)
        (y.1 ⟶[Complex A] z.1) (y.2 ⟶[Complex A] z.2) ≫
      (eComp (Complex A) x.1 y.1 z.1 ⊗ₘ eComp (Complex A) x.2 y.2 z.2) := by
  rw [TransportEnrichment.eComp_eq, tensor_μ]
  rfl

end SerrePositivity.DifferentialGraded
