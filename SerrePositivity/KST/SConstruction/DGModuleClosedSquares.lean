module
public import SerrePositivity.KST.SConstruction.DGModuleClosedOperations
public import SerrePositivity.InfinityCategories.Derived.DGFullSquareLift
public import SerrePositivity.InfinityCategories.Derived.DGModuleConePullback
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberPushout

/-! # 実有限操作の閉性で制限した dg 加群の標準四角形

概要：K(D) の実操作の条件を満たす全 dg 加群の内部で標準 cone/fiber 四角形を構成。
方針：四頂点の閉性から全単体を制限し、両普遍性を反映する。
規約：Hom end は変更しない。使われ方：ホモトピー表現可能部分の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : RightModule A D → Prop) (hP : DGModuleClosedOperations A D P)
variable {M N : ModuleCategory A D} (f : M ⟶ N)
variable (hM : P (ForgetEnrichment.to (Complex A) M))
variable (hN : P (ForgetEnrichment.to (Complex A) N))

include hM hN hP

/-- 標準 cone 四角形の四頂点は同じ実操作の条件を満たす。 -/
lemma dgModuleClosedConeVertices (i j : Fin 2) :
    P ((squareVertex (dgModuleConeSquare A D f) i j).obj 0) := by
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun t : (dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (dgModuleConeSquare_vertex00 A D f)).mpr (hM)
  · exact (congrArg (fun t : (dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (dgModuleConeSquare_vertex01 A D f)).mpr (hP.zero_mem)
  · exact (congrArg (fun t : (dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (dgModuleConeSquare_vertex10 A D f)).mpr (hN)
  · exact (congrArg (fun t : (dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (dgModuleConeSquare_vertex11 A D f)).mpr (hP.cone_mem f hM hN)

/-- 標準 fiber 四角形の四頂点は同じ実操作の条件を満たす。 -/
lemma dgModuleClosedFiberVertices (i j : Fin 2) :
    P ((squareVertex (dgModuleFiberSquare A D f) i j).obj 0) := by
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun t : (dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (dgModuleFiberSquare_vertex00 A D f)).mpr (hP.fiber_mem f hM hN)
  · exact (congrArg (fun t : (dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (dgModuleFiberSquare_vertex01 A D f)).mpr (hP.zero_mem)
  · exact (congrArg (fun t : (dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (dgModuleFiberSquare_vertex10 A D f)).mpr (hM)
  · exact (congrArg (fun t : (dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (dgModuleFiberSquare_vertex11 A D f)).mpr (hN)

/-- 実操作の条件を満たす加群の内部の実 cone 四角形。 -/
def dgModuleClosedConeSquare :=
  dgFullSquareLift A (RightModule A D) (P)
    (dgModuleConeSquare A D f) (dgModuleClosedConeVertices A D P hP f hM hN)

/-- 実操作の条件を満たす加群の内部の実 fiber 四角形。 -/
def dgModuleClosedFiberSquare :=
  dgFullSquareLift A (RightModule A D) (P)
    (dgModuleFiberSquare A D f) (dgModuleClosedFiberVertices A D P hP f hM hN)

/-- 条件付き加群の cone 四角形は内部でも押し出し。 -/
lemma dgModuleClosedConeSquare_isPushout :
    IsPushoutSquare (dgModuleClosedConeSquare A D P hP f hM hN) :=
  dgFullSquareLift_isPushout A _ _ _ _ (dgModuleConeSquare_isPushout A D f)

/-- 条件付き加群の cone 四角形は内部でも引き戻し。 -/
lemma dgModuleClosedConeSquare_isPullback :
    IsPullbackSquare (dgModuleClosedConeSquare A D P hP f hM hN) :=
  dgFullSquareLift_isPullback A _ _ _ _ (dgModuleConeSquare_isPullback A D f)

/-- 条件付き加群の fiber 四角形は内部でも引き戻し。 -/
lemma dgModuleClosedFiberSquare_isPullback :
    IsPullbackSquare (dgModuleClosedFiberSquare A D P hP f hM hN) :=
  dgFullSquareLift_isPullback A _ _ _ _ (dgModuleFiberSquare_isPullback A D f)

/-- 条件付き加群の fiber 四角形は内部でも押し出し。 -/
lemma dgModuleClosedFiberSquare_isPushout :
    IsPushoutSquare (dgModuleClosedFiberSquare A D P hP f hM hN) :=
  dgFullSquareLift_isPushout A _ _ _ _ (dgModuleFiberSquare_isPushout A D f)

end SerrePositivity.KST.SConstruction
