module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 元の dg 関手の tensor 作用
概要：二つの dg 関手から、元の tensor dg 圏の間の厳密 dg 関手を作る。
方針：対象は組、Hom 作用は元の二つの chain map の tensor とし、tensorμ の自然性を使う。
規約：全次数 Hom を保持し、小ささは要求しない。使われ方：高次入力の二回作用の束ね。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {C : Type v} {D : Type w} {E : Type z} {B : Type t}
  [DGCategory A C] [DGCategory A D] [DGCategory A E] [DGCategory A B]

/-- 元の二つの dg 関手の対象と全 Hom を tensor で同時に動かす。 -/
def dgTensorFunctor (F : DGFunctor A C E) (G : DGFunctor A D B) :
    DGFunctor A (DGTensorCategory A C D) (DGTensorCategory A E B) where
  obj x := (F.obj x.1, G.obj x.2)
  map x y := F.map x.1 y.1 ⊗ₘ G.map x.2 y.2
  map_id x := by
    rw [dgTensor_identity, dgTensor_identity, Category.assoc, tensorHom_comp_tensorHom,
      F.map_id, G.map_id]
  map_comp x y z := by
    rw [dgTensor_composition, dgTensor_composition, Category.assoc,
      tensorHom_comp_tensorHom, F.map_comp, G.map_comp,
      ← tensorHom_comp_tensorHom, ← Category.assoc, ← tensorμ_natural]
    simp only [Category.assoc]

/-- tensor 関手の全 Hom は、元の二つの Hom chain map の tensor そのもの。 -/
lemma dgTensorFunctor_map (F : DGFunctor A C E) (G : DGFunctor A D B)
    (x y : DGTensorCategory A C D) :
    (dgTensorFunctor A F G).map x y = F.map x.1 y.1 ⊗ₘ G.map x.2 y.2 := rfl

end SerrePositivity.KST.SConstruction
