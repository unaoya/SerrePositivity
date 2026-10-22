module
public import SerrePositivity.KST.SConstruction.DGEndIsoConjugation

/-! # 元の閉同型を保つ End 共役の全 Hom 可換式
概要：元の閉同型の順射は、元の End 作用と共役後の End 作用を全次数で結ぶ。
方針：前後合成の交換と元の閉同型の逆律を使う。
規約：閉零射だけに制限しない。使われ方：同じ代表加群への作用の自然な比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {x y : ClosedCategory R D} (e : x ≅ y)

/-- 元の閉同型の順射は、同じ共役前後の全 Hom 作用を結ぶ。 -/
lemma dgEndIsoHom_intertwining :
    dgEndIsoHom R e ≫ eHomWhiskerRight (Complex R) e.hom y =
      eHomWhiskerLeft (Complex R) x e.hom := by
  rw [dgEndIsoHom, Category.assoc, eHom_whisker_exchange,
    ← Category.assoc, ← eHomWhiskerRight_comp, e.hom_inv_id,
    eHomWhiskerRight_id, Category.id_comp]

end SerrePositivity.KST.SConstruction
