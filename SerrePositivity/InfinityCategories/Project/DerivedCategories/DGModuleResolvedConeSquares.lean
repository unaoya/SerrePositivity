module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactClassicalTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAllResolvedExact
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Suspension
/-!
概要：同じ全加群の実分解は標準 cone 四角形を保ち、零への cone は native 懸垂四角形となる。
方針：全加群実分解の完全性を K-7 の同じ関手へ戻し、実四角形をそのまま後合成する。
規約：入力加群の射影性を仮定せず、元の cone・零加群・全四角形を固定する。
使われ方：D-8 c3/c4 の shift・cone 比較。κ-compact 閉性自体は別に検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- K-7 の同じ実導来関手は完全。 -/
lemma dgConeModuleDerived_isExactFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgConeModuleDerived R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionInfinity_isExactFunctor R D

/-- 元の全加群 nerve の零頂点を同じ実分解は零頂点へ送る。 -/
lemma dgConeModuleDerived_preservesZeroVertices :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices (dgConeModuleDerived R D) := by
  let := dgConeModuleDerived_isExactFunctor R D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero

/-- 元の実 cone の全四角形を同じ実分解で写しても押し出し。 -/
lemma dgConeModuleDerived_coneSquare_isPushout {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare R D f ≫ dgConeModuleDerived R D) := by
  let := dgConeModuleDerived_isExactFunctor R D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := dgConeModuleDerived R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle R D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout R D f)

/-- 同じ実分解が写す標準 cone 四角形の頂点。 -/
lemma dgConeModuleDerived_coneSquare_vertex {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare R D f ≫ dgConeModuleDerived R D) 1 1 =
      dgConeModuleDerivedVertex R D (_root_.SerrePositivity.DifferentialGraded.moduleCone R D f) := by
  change (dgConeModuleDerived R D).app _ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare R D f) 1 1) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex11]
  rfl

/-- 元の加群から零加群への cone を、同じ実導来頂点の懸垂四角形として保持する。 -/
def dgConeModuleDerivedSuspensionSquare (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (dgConeModuleDerivedVertex R D M) where
  toZeroTriangle := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle R D (moduleToZero R D M)).map
    (dgConeModuleDerived R D) (dgConeModuleDerived_preservesZeroVertices R D)
  source_eq := by
    change (dgConeModuleDerived R D).app _
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare R D (moduleToZero R D M)) 0 0) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex00]
    rfl
  other_zero := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgConeModuleDerived R D).app _
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare R D (moduleToZero R D M)) 1 0))
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex10]
    exact dgConeModuleDerived_preservesZeroVertices R D _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero R D)
  isPushout := dgConeModuleDerived_coneSquare_isPushout R D _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
