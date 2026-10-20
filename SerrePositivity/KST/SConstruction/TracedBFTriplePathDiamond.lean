module
public import SerrePositivity.KST.SConstruction.TracedBFCoherentTriple
public import SerrePositivity.KST.SConstruction.CoherentPathInsertionDiamond

/-! # 元の三入力 BF 四面体の二切断を結ぶ実二単体
概要：三面を保存した同じ BF 四面体の全 Path 作用から、二つの切断順序の実二単体を得る。
方針：元の端点 Path に中間頂点一・二を加える二経路を同じ豊穣作用で写す。
規約：二単体も共通対角辺も元の作用の実像。独立な第四面との同一視は別工程。
使われ方：三入力の共有面を元の BF 写像空間の実二次元比較へ復号する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet Spectra
open scoped Simplicial
local instance tracedTriplePathSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の同じ実四面体の、初頂点から終頂点への全 Path の実豊穣作用。 -/
def monicKTracedCoherentTriplePathMap :=
  (monicKTracedCoherentTripleData F f g h).simplex.map
    (.mk (ULift.up (0 : Fin 4))) (.mk (ULift.up (3 : Fin 4)))

/-- 中間頂点一を先に加える経路の、元の豊穣作用内の同じ実二単体。 -/
def monicKTracedCoherentTripleFirstPathTriangle :=
  coherentDoubleInsertMappedFirstTriangle (monicKTracedCoherentTriplePathMap F f g h)
    (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 1 from by decide)
    (show (ULift.up (1 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide)
    (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 2 from by decide)
    (show (ULift.up (2 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide)
    (coherentEndpointPath (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide))

/-- 中間頂点二を先に加える経路の、同じ豊穣作用内の実二単体。 -/
def monicKTracedCoherentTripleSecondPathTriangle :=
  coherentDoubleInsertMappedSecondTriangle (monicKTracedCoherentTriplePathMap F f g h)
    (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 1 from by decide)
    (show (ULift.up (1 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide)
    (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 2 from by decide)
    (show (ULift.up (2 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide)
    (coherentEndpointPath (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide))

end SerrePositivity.KST.SConstruction
