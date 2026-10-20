module
public import SerrePositivity.KST.SConstruction.TracedBFTripleCompositionDiamond
public import SerrePositivity.KST.SConstruction.TracedBFFirstWhiskerRecovery
public import SerrePositivity.KST.SConstruction.TracedBFSecondWhiskerRecovery
public import SerrePositivity.KST.SConstruction.CompositionDiamondEdgeTransport

/-! # 元の BF 比較三辺への三入力実三角形対の相対移送
概要：元の全二三角形を終端に保持し、三辺を元の BF 比較辺とその実合成へ移す。
方針：保存した回収円柱を全境界へ貼り、元の共通対角辺を定数円柱で固定する。
規約：生成された第四辺は固定する。独立に指定した第四合成面との一致は未証明。
使われ方：元の raw 高次 prism と独立の第四面を照合するための実比較データ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tracedTripleEdgeTransportSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance tracedTripleEdgeTransportMappingKan (A B : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom A B) := OmegaSpectrum.mappingSpace_kanComplex A B
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 第一の元の BF 比較辺から元の保存面の復号辺への同じ全端点固定円柱。 -/
def monicKTracedTripleLowerRecoveryCylinder : EndpointFixedEdgeCylinder
    (monicKTracedSpectrumCompositionEdge F f (g ≫ h))
    (coherentTriangleMappingEdge (monicKTracedSpectrumMap F f)
      (monicKTracedSpectrumMap F (g ≫ h)) (monicKTracedSpectrumMap F (f ≫ g ≫ h))
      (monicKTracedCoherentComposition F f (g ≫ h))) :=
  ⟨monicKTracedCompositionRecoveryCylinder F f (g ≫ h),
    monicKTracedCompositionRecoveryCylinder_relative F f (g ≫ h)⟩

/-- 第一の元の BF whisker から元の保存面の whisker への同じ全端点固定円柱。 -/
def monicKTracedTripleFirstRecoveryCylinder : EndpointFixedEdgeCylinder
    (monicKTracedNativeFirstWhisker F f g h)
    (monicKTracedCoherentTripleFirstWhisker F f g h) :=
  ⟨monicKTracedFirstWhiskerRecovery F f g h,
    monicKTracedFirstWhiskerRecovery_relative F f g h⟩

/-- 第二の元の BF whisker から元の保存面の whisker への同じ全端点固定円柱。 -/
def monicKTracedTripleSecondRecoveryCylinder : EndpointFixedEdgeCylinder
    (monicKTracedNativeSecondWhisker F f g h)
    (monicKTracedCoherentTripleSecondWhisker F f g h) :=
  ⟨monicKTracedSecondWhiskerRecovery F f g h,
    monicKTracedSecondWhiskerRecovery_relative F f g h⟩

/-- 元の BF 三辺と同じ生成第四辺を持ち、元の共通対角辺を共有する実三角形対。 -/
def monicKTracedNativeTripleCompositionDiamond :=
  compositionDiamondEdgeTransport
    (monicKTracedTripleLowerRecoveryCylinder F f g h)
    (monicKTracedTripleFirstRecoveryCylinder F f g h)
    (endpointFixedEdgeCylinderRefl (monicKTracedCoherentTripleGeneratedEdge F f g h))
    (monicKTracedTripleSecondRecoveryCylinder F f g h)
    (monicKTracedCoherentTripleCompositionDiamond F f g h)

/-- 第一の全三角形を元の同じ全三角形へ戻す、三辺回収円柱を持つ実比較。 -/
def monicKTracedNativeTripleFirstComparison :=
  compositionDiamondEdgeTransportFirstComparison
    (monicKTracedTripleLowerRecoveryCylinder F f g h)
    (monicKTracedTripleFirstRecoveryCylinder F f g h)
    (endpointFixedEdgeCylinderRefl (monicKTracedCoherentTripleGeneratedEdge F f g h))
    (monicKTracedTripleSecondRecoveryCylinder F f g h)
    (monicKTracedCoherentTripleCompositionDiamond F f g h)

/-- 第二の全三角形も、元の同じ全三角形を終端に保持する実比較を持つ。 -/
def monicKTracedNativeTripleSecondComparison :=
  compositionDiamondEdgeTransportSecondComparison
    (monicKTracedTripleLowerRecoveryCylinder F f g h)
    (monicKTracedTripleFirstRecoveryCylinder F f g h)
    (endpointFixedEdgeCylinderRefl (monicKTracedCoherentTripleGeneratedEdge F f g h))
    (monicKTracedTripleSecondRecoveryCylinder F f g h)
    (monicKTracedCoherentTripleCompositionDiamond F f g h)

/-- 相対移送は元の同じ共通対角辺をそのまま保持する。 -/
lemma monicKTracedNativeTripleCompositionDiamond_diagonal :
    (monicKTracedNativeTripleCompositionDiamond F f g h).diagonal =
      (monicKTracedCoherentTripleCompositionDiamond F f g h).diagonal := rfl

/-- 第一の全比較は、元の共通対角辺の全区間を全比較時刻で固定する。 -/
lemma monicKTracedNativeTripleFirstComparison_diagonal :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedNativeTripleFirstComparison F f g h).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm
        (monicKTracedCoherentTripleCompositionDiamond F f g h).diagonal.edge :=
  compositionDiamondEdgeTransportFirstComparison_diagonal _ _ _ _ _

/-- 第二の全比較でも、同じ元の共通対角辺を全時刻で固定する。 -/
lemma monicKTracedNativeTripleSecondComparison_diagonal :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedNativeTripleSecondComparison F f g h).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm
        (monicKTracedCoherentTripleCompositionDiamond F f g h).diagonal.edge :=
  compositionDiamondEdgeTransportSecondComparison_diagonal _ _ _ _ _

/-- 第一比較の下辺側面は、元の同じ BF 比較辺の全回収円柱。 -/
lemma monicKTracedNativeTripleFirstComparison_lower :
    (stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedNativeTripleFirstComparison F f g h).h =
      (monicKTracedCompositionRecoveryCylinder F f (g ≫ h)).h :=
  compositionDiamondEdgeTransportFirstComparison_face _ _ _ _ _ 2

/-- 第一比較の上辺側面も、元の同じ BF whisker の全回収円柱。 -/
lemma monicKTracedNativeTripleFirstComparison_upper :
    (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedNativeTripleFirstComparison F f g h).h =
      (monicKTracedFirstWhiskerRecovery F f g h).h :=
  compositionDiamondEdgeTransportFirstComparison_face _ _ _ _ _ 0

/-- 第二比較の上辺側面は、元の同じ第二 BF whisker の全回収円柱。 -/
lemma monicKTracedNativeTripleSecondComparison_upper :
    (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedNativeTripleSecondComparison F f g h).h =
      (monicKTracedSecondWhiskerRecovery F f g h).h :=
  compositionDiamondEdgeTransportSecondComparison_face _ _ _ _ _ 0

/-- 第二比較の下辺は、元の同じ生成された第四辺全体を全時刻固定する。 -/
lemma monicKTracedNativeTripleSecondComparison_lower :
    (stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedNativeTripleSecondComparison F f g h).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm
        (monicKTracedCoherentTripleGeneratedEdge F f g h).edge :=
  compositionDiamondEdgeTransportSecondComparison_face _ _ _ _ _ 2

/-- 第一比較の終端は、元の第一 Path 二単体の全像そのもの。 -/
lemma monicKTracedNativeTripleFirstComparison_original :
    SSet.ι₁ ≫ (monicKTracedNativeTripleFirstComparison F f g h).h =
      SSet.yonedaEquiv.symm
        ((eqToHom (monicKTracedCoherentTripleMappingSpace_eq F f g h)).app (Opposite.op ⦋2⦌)
          (monicKTracedCoherentTripleFirstPathTriangle F f g h).simplex) := by
  rw [SSet.Homotopy.h₁, monicKTracedCoherentTripleCompositionDiamond_first_image]

/-- 第二比較の終端も、元の第二 Path 二単体の同じ全像そのもの。 -/
lemma monicKTracedNativeTripleSecondComparison_original :
    SSet.ι₁ ≫ (monicKTracedNativeTripleSecondComparison F f g h).h =
      SSet.yonedaEquiv.symm
        ((eqToHom (monicKTracedCoherentTripleMappingSpace_eq F f g h)).app (Opposite.op ⦋2⦌)
          (monicKTracedCoherentTripleSecondPathTriangle F f g h).simplex) := by
  rw [SSet.Homotopy.h₁, monicKTracedCoherentTripleCompositionDiamond_second_image]

end SerrePositivity.KST.SConstruction
