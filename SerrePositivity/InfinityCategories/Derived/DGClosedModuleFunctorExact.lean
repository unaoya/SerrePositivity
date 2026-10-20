module
public import SerrePositivity.InfinityCategories.Derived.DGModuleClosedPropertyStability
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Derived.DGFullFunctorRestriction
public import SerrePositivity.InfinityCategories.Derived.DGFullInclusionExactReflection
/-!
概要：標準演算で閉じる加群部分圏間への実 dg 関手の完全性。
方針：周囲の dg 関手の完全性と、元の包含との厳密な可換性を使う。
規約：像の対象条件の閉性は反映には不要。使われ方：β5 の Perf の実完全包含。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 演算で閉じた始域の加群部分圏への実 dg 制限は、全 cofiber 列を保存する。 -/
theorem dgClosedModuleFunctorNerve_isExactFunctor
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (P : RightModule R D → Prop) (Q : RightModule R E → Prop)
    (hP : DGModuleClosedProperty R D P) (hF : ∀ M, P M → Q (F.obj M)) :
    IsExactFunctor (dgNerve.map (dgFullFunctorRestriction R _ _ F P Q hF)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) P
  let J := dgFullSubcategoryInclusion R (RightModule R E) Q
  let G := dgFullFunctorRestriction R _ _ F P Q hF
  have hd : G.comp J = I.comp F := dgFullFunctorRestriction_inclusion R _ _ F P Q hF
  have he : dgNerve.map G ≫ dgNerve.map J = dgNerve.map I ≫ dgNerve.map F := by
    simpa only [dgNerve.map_comp] using congrArg (fun H => dgNerve.map H) hd
  let := dgClosedModuleInclusion_isExactFunctor R D P hP
  let := dgModuleFunctorNerve_isExactFunctor R D E F
  have : IsExactFunctor (dgNerve.map G ≫ dgNerve.map J) :=
    he.symm ▸ isExactFunctor_comp (dgNerve.map I) (dgNerve.map F)
  exact isExactFunctor_of_postcomp_dgFullInclusion R (RightModule R E) Q (dgNerve.map G)
end SerrePositivity.InfinityCategories
