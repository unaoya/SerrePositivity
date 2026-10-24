module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCommonMap
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.DGNerve.Quasicategory
/-!
概要：混在宇宙の dg 関手の共通 nerve 写像は零頂点を保存する。
方針：native nerve の零保存を、対象宇宙比較の実同型で共役する。
規約：始域・終域に Small や安定性を仮定しない。
使われ方：全加群間および前三角始域の混在宇宙の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w t
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {D : Type v} {E : Type w}
  [DGCategory R D] [DGCategory R E]

lemma dgNerveCommonMap_preservesZeroVertices (F : DGFunctor R D E) :
    PreservesZeroVertices (dgNerveCommonMap.{u, v, w, t} F) := by
  rw [dgNerveCommonMap_lifted]
  let d := dgNerveUniverseLiftIso.{u, v, max u v w t} R D
  let e := dgNerveUniverseLiftIso.{u, w, max u v w t} R E
  let := isExactFunctor_of_isQCatEquivalence (qCatEquivalenceOfIso d).isQCatEquivalence
  let := isExactFunctor_of_isQCatEquivalence (qCatEquivalenceOfIso e.symm).isQCatEquivalence
  intro x hx
  exact IsExactFunctor.preservesZero (F := e.inv) _
    (dgFunctorNerve_preservesZeroVertices
      (dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} F) _
      (IsExactFunctor.preservesZero (F := d.hom) x hx))

end SerrePositivity.InfinityCategories
