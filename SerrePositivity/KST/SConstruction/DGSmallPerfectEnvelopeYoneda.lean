module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelope
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 元の全代表を持つ小模型への厳密 Yoneda
概要：元の dg 圏から、同じ代表対象を実際に含む小模型への厳密 dg 関手を構成する。
方針：元の Yoneda の全 Hom 作用と関手法則をそのまま使う。
規約：H⁰ での代表選択を使わない。使われ方：元の右対象 End から具体的商 End への射。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (J : Type w) (X : J → PerfectDGModule R D)

/-- 元の同じ全代表と全 Yoneda Hom 作用を保持する、小模型への厳密 dg 関手。 -/
def dgSmallPerfectEnvelopeYoneda : DGFunctor R D (DGSmallPerfectEnvelope R D J X) where
  obj := dgSmallPerfectEnvelopeRepresentable R D J X
  map x y := (dgYoneda R D).map x y
  map_id x := (dgYoneda R D).map_id x
  map_comp x y z := (dgYoneda R D).map_comp x y z

end SerrePositivity.KST.SConstruction
