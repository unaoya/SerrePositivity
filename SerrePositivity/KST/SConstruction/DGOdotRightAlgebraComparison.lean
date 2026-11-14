module
public import SerrePositivity.KST.SConstruction.DGOdotAlgebraRealization

/-! # 元の右代数射と同じ商 End 射の厳密同定
概要：右代数射の一対象 dg 関手を、構成済みの元の右 End 射へ照合する。
方針：右代数の元の指定対象への全 Hom 恒等射を作り、基礎鎖写像の回収式を使う。
規約：元の右代数・実射・指定対象を保持。使われ方：LT 四角形の右側の元の辺。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R]

/-- 元の右加群用一対象圏から、その元の指定対象 End への全 Hom 恒等射。 -/
def dgAlgebraToOriginalEnd (B : Mon (Complex R)) :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
      (EndomorphismObject (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)) where
  obj _ := EndomorphismObject.point
  map _ _ := 𝟙 _
  map_id _ := by
    change eId (Complex R) (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B) ≫ 𝟙 _ = _
    exact Category.comp_id _
  map_comp _ _ _ := by
    change (eComp (Complex R) (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
      (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star) (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star)) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp (Complex R)
          (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
          (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star) (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star)
    rw [id_tensorHom_id, Category.comp_id, Category.id_comp]

/-- 元の End 射の反転代数化は、右加群用圏へ戻すと同じ全 Hom 射を回収する。 -/
lemma dgAlgebraEndMap_realization (B : Mon (Complex R))
    (D : Type v) [DGCategory R D] (y : D)
    (F : DGFunctor R
      (EndomorphismObject (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B))
      (EndomorphismObject y)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R ((dgAlgebraRightEndIso R B (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star)).hom ≫
      LocalizingInvariants.dgEndAlgebraMap R
        (EndomorphismObject (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B))ᵒᵖ
        F.op (Opposite.op EndomorphismObject.point))).comp
      (dgOdotEndAlgebraOppositeInclusion R (EndomorphismObject y) EndomorphismObject.point) =
        (dgAlgebraToOriginalEnd R B).comp F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x z
  change ((𝟙 _) ≫ F.map EndomorphismObject.point EndomorphismObject.point) ≫ 𝟙 _ =
    𝟙 _ ≫ F.map EndomorphismObject.point EndomorphismObject.point
  rw [Category.comp_id]

variable (d : DGOdotInput R)

/-- 元の右代数射を ⊙ の実 End 模型へ写すと、同じ元の右 End 射を厳密に回収する。 -/
lemma dgOdotRightMap_toEnd :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotRightMap R d)).comp (dgOdotAlgebraToEnd R d) =
      (dgAlgebraToOriginalEnd R d.right).comp (dgOdotRightEndMap R d) :=
  dgAlgebraEndMap_realization R d.right (dgOdotQuotientInput R d).quotientObject
    ((dgOdotQuotientInput R d).projection.obj (dgOdotQuotientInput R d).point)
    (dgOdotRightEndMap R d)

end SerrePositivity.KST.SConstruction
