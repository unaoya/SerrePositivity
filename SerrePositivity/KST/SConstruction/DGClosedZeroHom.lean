module
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # 閉零対象の全 Hom 複体と実定数零 dg 関手
概要：元の閉零対象への全 Hom 複体は実零複体であり、元の対象値を持つ零関手を作れる。
方針：共変代表加群の加法的な閉零制限で零性を移し、その Hom 零性で関手法則を得る。
規約：nerve 内の零対象性だけでは代用しない。使われ方：gluing の実右軸包含。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] {C : Type v} [DGCategory R C]
  (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z))

include hz in
/-- 元の閉零対象への、全整数次数を持つ Hom 複体は実零対象。 -/
lemma dgHom_isZero_of_closed_zero_target (x : C) : IsZero (homObject R C x z) :=
  ((leftRepresentable R x).onClosed ⋙ closedToComplex R).map_isZero hz

include hz in
/-- 元の閉零対象の同じ豊穣単位は、実鎖写像として零。 -/
lemma dgClosedZero_eId : eId (Complex R) z = 0 :=
  (dgHom_isZero_of_closed_zero_target R z hz z).eq_of_tgt _ _

/-- 元の閉零対象の全 Hom を零作用とする、同じ対象値の実 dg 定数関手。 -/
def dgClosedZeroFunctor (P : Type w) [DGCategory R P] : DGFunctor R P C where
  obj _ := z
  map _ _ := 0
  map_id _ := (dgHom_isZero_of_closed_zero_target R z hz z).eq_of_tgt _ _
  map_comp _ _ _ := (dgHom_isZero_of_closed_zero_target R z hz z).eq_of_tgt _ _

/-- 同じ実零関手は、指定した元の閉零対象をそのまま保持する。 -/
lemma dgClosedZeroFunctor_obj (P : Type w) [DGCategory R P] (x : P) :
    (dgClosedZeroFunctor R z hz P).obj x = z := rfl

/-- 同じ実零関手の全 Hom 作用は、指定した零鎖写像そのもの。 -/
lemma dgClosedZeroFunctor_map (P : Type w) [DGCategory R P] (x y : P) :
    (dgClosedZeroFunctor R z hz P).map x y = 0 := rfl

include hz in
/-- 代表右加群の閉零対象からの全 Hom end は、元の零 Hom 複体から実零となる。 -/
lemma dgRepresentableClosedZeroHom [Small.{u} C] (N : RightModule R C) :
    IsZero (homObject R (RightModule R C) (representable R z) N) :=
  moduleHom_isZero_src R C (representable R z) N
    (fun x => dgHom_isZero_of_closed_zero_target R z hz x)

end SerrePositivity.KST.SConstruction
