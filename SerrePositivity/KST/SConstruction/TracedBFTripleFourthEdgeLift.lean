module
public import SerrePositivity.KST.SConstruction.TracedBFTripleRawBoundaryFaces
public import SerrePositivity.KST.SConstruction.CompositionDiamondFourthEdgeTransport

/-! # 元の全 raw 比較から指定 BF 四辺の実三角形対へ
概要：第四辺の全 raw 比較が与えられれば、指定 BF 四辺と同じ対角辺を持つ実三角形対を作る。
方針：全 raw 円柱を端点固定で持ち上げ、第二全三角形だけを相対移送する。
規約：第一全三角形は厳密に保持する。raw 比較の存在は未証明の入力として明示する。
使われ方：raw 高次 prism の到着後、既存の全三角形と元の指定四辺を接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tracedFourthEdgeSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance tracedFourthEdgeMappingKan (A B : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom A B) := OmegaSpectrum.mappingSpace_kanComplex A B
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)
  (H : MonicKTracedTripleRawComparison F f g h)

/-- 元の BF 四辺と共通対角辺を持つ実三角形対。元の raw 比較を明示的な入力に持つ。 -/
def monicKTracedTripleCompositionDiamondFromRaw :=
  compositionDiamondFourthEdgeTransport (monicKTracedTripleFourthEdgeLiftData F f g h H).val
    (monicKTracedNativeTripleCompositionDiamond F f g h)

/-- 元の raw 円柱を射影に持つ持ち上げで、第二三角形を元の指定左辺へ移す。 -/
def monicKTracedTripleFourthTriangleFromRaw :=
  (monicKTracedTripleCompositionDiamondFromRaw F f g h H).second

/-- 第一の元の全三角形は、第四辺の移送で全く変更しない。 -/
lemma monicKTracedTripleCompositionDiamondFromRaw_first :
    (monicKTracedTripleCompositionDiamondFromRaw F f g h H).first.simplex =
      (monicKTracedNativeTripleCompositionDiamond F f g h).first.simplex :=
  compositionDiamondFourthEdgeTransport_first _ _

/-- 元の共通対角辺も同じ全辺を厳密に保持する。 -/
lemma monicKTracedTripleCompositionDiamondFromRaw_diagonal :
    (monicKTracedTripleCompositionDiamondFromRaw F f g h H).diagonal =
      (monicKTracedNativeTripleCompositionDiamond F f g h).diagonal :=
  compositionDiamondFourthEdgeTransport_diagonal _ _

/-- 第二の全三角形を、移送前の元の第二全三角形へ戻す実比較。 -/
def monicKTracedTripleFourthTriangleComparison :=
  compositionDiamondFourthEdgeTransportComparison
    (monicKTracedTripleFourthEdgeLiftData F f g h H).val
    (monicKTracedNativeTripleCompositionDiamond F f g h)

/-- 第二三角形の下面の全 raw 射影は、入力した元の同じ全 raw 円柱そのもの。 -/
lemma monicKTracedTripleFourthTriangleComparison_lower_projection :
    (stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleFourthTriangleComparison F f g h H).h ≫
          kRawMappingProjection (F.obj w) (F.obj z) = H.homotopy.h := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ kRawMappingProjection (F.obj w) (F.obj z))
      (compositionDiamondFourthEdgeTransportComparison_face
        (monicKTracedTripleFourthEdgeLiftData F f g h H).val
        (monicKTracedNativeTripleCompositionDiamond F f g h) 2)).trans
      (monicKTracedTripleFourthEdgeLiftData_projection F f g h H))

/-- 第二三角形の上辺全体は、全比較時刻で元の同じ BF whisker に固定する。 -/
lemma monicKTracedTripleFourthTriangleComparison_upper :
    (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleFourthTriangleComparison F f g h H).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫
        SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge :=
  compositionDiamondFourthEdgeTransportComparison_face _ _ 0

/-- 第二三角形の対角辺全体も、全比較時刻で元の同じ対角辺に固定する。 -/
lemma monicKTracedTripleFourthTriangleComparison_diagonal :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleFourthTriangleComparison F f g h H).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm
        (monicKTracedNativeTripleCompositionDiamond F f g h).diagonal.edge :=
  compositionDiamondFourthEdgeTransportComparison_face _ _ 1

/-- 第二三角形から元の保存済み全三角形へ戻る、両実比較円柱を保持する有限列。 -/
def monicKTracedTripleFourthTriangleOriginalChain : FamilyHomotopyChain
    (SSet.yonedaEquiv.symm (monicKTracedTripleFourthTriangleFromRaw F f g h H).simplex)
    (SSet.yonedaEquiv.symm
      (monicKTracedCoherentTripleCompositionDiamond F f g h).second.simplex) :=
  .cons (monicKTracedTripleFourthTriangleComparison F f g h H)
    (familyHomotopyChainSingle (monicKTracedNativeTripleSecondComparison F f g h))

/-- 元の二比較円柱は、同じ有限列の二つの全区間として厳密に保存される。 -/
lemma monicKTracedTripleFourthTriangleOriginalChain_trace :
    familyHomotopyChainTrace (monicKTracedTripleFourthTriangleOriginalChain F f g h H) =
      [(monicKTracedTripleFourthTriangleComparison F f g h H).h,
        (monicKTracedNativeTripleSecondComparison F f g h).h] := rfl

end SerrePositivity.KST.SConstruction
