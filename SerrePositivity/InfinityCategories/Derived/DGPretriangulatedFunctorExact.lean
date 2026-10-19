module
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorLiftedExact
public import SerrePositivity.InfinityCategories.Derived.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Stable.UniverseExactFunctor

/-! # 前三角 dg 圏間の native nerve の関手の完全性

概要：前三角 dg 圏間の任意の dg 関手の元の宇宙の nerve は完全。
方針：対象宇宙を上げた関手を実宇宙同型で照合し、零対象と cofiber 保存を降下する。
規約：平坦性や模型圏の仮定を追加しない。使われ方：β3 の実商関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A D E)

omit [Small.{u} D] [Small.{u} E] in
/-- 対象宇宙を上げた dg 関手は、実宇宙同型で元の nerve の ULift に一致。 -/
lemma dgUniverseLiftFunctor_nerve_conjugate :
    (dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D).hom ≫
      dgNerve.map (dgUniverseLiftFunctor.{u, v, v, max (u + 1) v, max (u + 1) v} F) ≫
        (dgNerveUniverseLiftIso A E).inv =
      (SSet.uliftFunctor.{max (u + 1) v, max u v}).map (dgNerve.map F) := by
  ext n s
  apply ULift.ext
  apply Simplex.ext
  rfl

/-- 前三角 dg 圏間の任意の dg 関手の native nerve は完全。 -/
theorem dgPretriangulatedFunctor_isExactFunctor
    [IsDGPretriangulated A D] [IsDGPretriangulated A E] :
    IsExactFunctor (dgNerve.map F) := by
  apply isExactFunctor_of_ulift.{max u v, max (u + 1) v}
  let := dgPretriangulatedFunctorLifted_isExactFunctor A D E F
  let := isExactFunctor_of_isQCatEquivalence
    (qCatEquivalenceOfIso (dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D)).isQCatEquivalence
  let := isExactFunctor_of_isQCatEquivalence
    (qCatEquivalenceOfIso (dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A E).symm).isQCatEquivalence
  rw [← dgUniverseLiftFunctor_nerve_conjugate A D E F]
  infer_instance

end SerrePositivity.InfinityCategories
