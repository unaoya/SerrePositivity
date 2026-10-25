module
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactClassicalTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleAllResolvedExact
public import SerrePositivity.InfinityCategories.Stable.Suspension
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- K-7 の同じ実導来関手は完全。 -/
lemma dgConeModuleDerived_isExactFunctor : IsExactFunctor (dgConeModuleDerived R D) :=
  dgModuleResolutionInfinity_isExactFunctor R D

/-- 元の全加群 nerve の零頂点を同じ実分解は零頂点へ送る。 -/
lemma dgConeModuleDerived_preservesZeroVertices :
    PreservesZeroVertices (dgConeModuleDerived R D) := by
  let := dgConeModuleDerived_isExactFunctor R D
  exact IsExactFunctor.preservesZero

/-- 元の実 cone の全四角形を同じ実分解で写しても押し出し。 -/
lemma dgConeModuleDerived_coneSquare_isPushout {M N : ModuleCategory R D} (f : M ⟶ N) :
    IsPushoutSquare (dgModuleConeSquare R D f ≫ dgConeModuleDerived R D) := by
  let := dgConeModuleDerived_isExactFunctor R D
  exact IsExactFunctor.preservesCofiber (F := dgConeModuleDerived R D)
    (dgModuleConeZeroTriangle R D f) (dgModuleConeSquare_isPushout R D f)

/-- 同じ実分解が写す標準 cone 四角形の頂点。 -/
lemma dgConeModuleDerived_coneSquare_vertex {M N : ModuleCategory R D} (f : M ⟶ N) :
    squareVertex (dgModuleConeSquare R D f ≫ dgConeModuleDerived R D) 1 1 =
      dgConeModuleDerivedVertex R D (moduleCone R D f) := by
  change (dgConeModuleDerived R D).app _ (squareVertex (dgModuleConeSquare R D f) 1 1) = _
  rw [dgModuleConeSquare_vertex11]
  rfl

/-- 元の加群から零加群への cone を、同じ実導来頂点の懸垂四角形として保持する。 -/
def dgConeModuleDerivedSuspensionSquare (M : ModuleCategory R D) :
    SuspensionSquare (dgConeModuleDerivedVertex R D M) where
  toZeroTriangle := (dgModuleConeZeroTriangle R D (moduleToZero R D M)).map
    (dgConeModuleDerived R D) (dgConeModuleDerived_preservesZeroVertices R D)
  source_eq := by
    change (dgConeModuleDerived R D).app _
      (squareVertex (dgModuleConeSquare R D (moduleToZero R D M)) 0 0) = _
    rw [dgModuleConeSquare_vertex00]
    rfl
  other_zero := by
    change IsZeroVertex ((dgConeModuleDerived R D).app _
      (squareVertex (dgModuleConeSquare R D (moduleToZero R D M)) 1 0))
    rw [dgModuleConeSquare_vertex10]
    exact dgConeModuleDerived_preservesZeroVertices R D _ (dgModuleNerveZeroVertex_isZero R D)
  isPushout := dgConeModuleDerived_coneSquare_isPushout R D _

end SerrePositivity.InfinityCategories
