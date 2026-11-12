module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.KST.SConstruction.DGKUniverseLiftSmall

/-! # 元の dg 圏を共通対象宇宙の固定始域へ入れる
概要：対象のラベルだけを持ち上げ、元の Small 性と全 Hom 複体を保つ。
方針：D の DGUniverseLift を同じ固定 PerfDGInput に束ねる。
規約：Perf 全体の Small 性は仮定しない。使われ方：実代数と対角商の S 内図式。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の全 Hom を持つ宇宙持ち上げを、同じ固定 dg 始域の実入力へ束ねる。 -/
def dgKUniverseInput : PerfDGInput.{u, max v w} R :=
  perfDGInputOf R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, w} D)

end SerrePositivity.KST.SConstruction
