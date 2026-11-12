module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberBoundarySolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ReplacementLocality

/-! # 標準 fiber の境界の明示解を挿入したデータ

概要：解いた先頭成分と N 側成分を左右の零未知データへ挿入する。
方針：共通の型付き解を生の対象へ移し、二つの集合の成分だけ置き換える。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：全方程式と貼合せを検証する候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 概要：Left 側の対象に移した先頭・N 側の解を比較証明とともに保持する。
方針：型付き解の二つの端点を境界の生の対象へ移す。
規約：HA Proposition 1.3.1.10。使われ方：候補データへの挿入と型付き解との比較。 -/
opaque dgModuleFiberBoundaryLeftNative {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    ({a : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n
        + 1) //
      HEq a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f b hb)}) ×
    ({d : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n) //
      HEq d (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownN A D f b hb)}) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := A) (D := RightModule A D) (rfl)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_apex A D f b hb).symm rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f b
        hb),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := A) (D := RightModule A D) (rfl)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_N A D f b hb).symm rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownN A D f b hb)⟩

/-- 概要：Left 側の零未知データに明示解 a,d を挿入した候補データ。
方針：先頭集合と N を加えた集合の二成分を順に置き換える。
規約：HA Proposition 1.3.1.10。使われ方：直接の境界充填の候補。全方程式は別途検証する。 -/
def dgModuleFiberBoundaryLeftCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n + 3) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b).replaceFixed (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree]; push_cast; omega)
    (dgModuleFiberBoundaryLeftNative A D f b hb).1.val).replaceFixed
      (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n)
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))]; omega)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_min _ _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_max _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))]
          dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree]
          push_cast
          omega)
      (dgModuleFiberBoundaryLeftNative A D f b hb).2.val

/-- 概要：Right 側の対象に移した先頭・N 側の解を比較証明とともに保持する。
方針：型付き解の二つの端点を境界の生の対象へ移す。
規約：HA Proposition 1.3.1.10。使われ方：候補データへの挿入と型付き解との比較。 -/
opaque dgModuleFiberBoundaryRightNative {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    ({a : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n
        + 1) //
      HEq a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f b hb)}) ×
    ({d : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n) //
      HEq d (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownN A D f b hb)}) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource_right_eq
    A D f b).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_apex A D f b hb).symm rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f
        b hb),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := A) (D := RightModule A D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource_right_eq A D f b).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_N A D f b hb).symm rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownN A D f b
        hb)⟩

/-- 概要：Right 側の零未知データに明示解 a,d を挿入した候補データ。
方針：先頭集合と N を加えた集合の二成分を順に置き換える。
規約：HA Proposition 1.3.1.10。使われ方：直接の境界充填の候補。全方程式は別途検証する。 -/
def dgModuleFiberBoundaryRightCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n + 3) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b).replaceFixed (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree]; push_cast; omega)
    (dgModuleFiberBoundaryRightNative A D f b hb).1.val).replaceFixed
      (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n)
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))]; omega)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_min _ _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_max _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))]
          dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree]
          push_cast
          omega)
      (dgModuleFiberBoundaryRightNative A D f b hb).2.val

end SerrePositivity.InfinityCategories.Project.DerivedCategories
