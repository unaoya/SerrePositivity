module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFFiberComparison
public import SerrePositivity.KST.NonConnective.DGKappaNativeStructure

/-!
概要：補助経路として、同じ有限 BF 四角形と実 cone の零性から、元の固定 K の構造辺へ接続する。
方針：未完備全 S• fibration を同じ BF 四角形へ渡し、同じ実 loop 同型の逆辺を使う。
規約：有限 BF 供給・共終性・全 S• fibration に条件付き。固定 K の Sp 引き戻し性は仮定しない。
使われ方：K-7 c5・d3 の同じ元の実 fibration 辺の供給口を放電する利用側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance nativeBFLoopSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance nativeBFLoopSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hBF : dgKappaNativeBFSquareComparison R D I)
  (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : DGKappaZeroInput R D I)
  (hS : ∀ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} r)))

include hS in
/-- 概要：同じ未完備全 S• fibration に条件付きで、供給された同じ BF 四角形は引き戻し。
方針：同じ全正段の全図式比較を元の実 fiber 比較の検出へ適用する。
規約：完備化後の固定 K 四角形については主張しない。hS の証明は K-6 の残り。
使われ方：同じ元の実商と cone による実 loop 四角形。 -/
theorem dgKappaNativeBFSquare_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgKappaNativeBFSquare R D I hBF) :=
  dgKappaNativeBFK_isPullback_of_positive_spaceEvaluation R D I hBF
    (fun r => dgKappaNativeBF_spaceEvaluation_isPullback R D I hBF r (hS r))

/-- 概要：同じ BF 四角形は同じ未完備実商 K の実 loop 四角形。
方針：同じ実零角・同じ cone の零性と、未完備全 S• 比較からの引き戻しを使う。
規約：有限 BF・共終性・実零所属・全 S• fibration に条件付き。
使われ方：元の未完備実核 K から同じ実商の native loop への実比較辺。 -/
def dgKappaNativeBFLoopSquare :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeSuspensionCategory R D I)))) where
  square := dgKappaNativeBFSquare R D I hBF
  zero_corner := dgKappaNativeBFSquare_zero_corner R D I hBF
  target_eq := dgKappaNativeBFSquare_target R D I hBF
  other_zero := (dgKappaNativeBFSquare_middle R D I hBF).symm ▸
    dgKappaNativeResolvedConeK_isZeroVertex R D I hcofinal Z
  isPullback := dgKappaNativeBFSquare_isPullback R D I hBF hS

/-- 概要：同じ実 loop 比較同型の逆を表す実辺を保持する。
方針：Sp 正本の同じ native loop 同型の逆の代表辺を取る。
規約：同じ loop 四角形からの辺であり、別の fibration 辺は入力しない。
使われ方：K-7 の構造辺へ渡す実未完備比較。 -/
def dgKappaNativeBFLoopInverseEdge :
    Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (dgKappaNativeBFLoopSquare R D I hBF hcofinal Z hS).vertex
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
          (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))))) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (OmegaSpectrum.nativeLoopVertexIso
      (dgKappaNativeBFLoopSquare R D I hBF hcofinal Z hS)).inv)

/-- 概要：同じ逆比較辺は元の実 loop 同型の逆そのものを表す。
方針：同じ代表辺の選択仕様を回収する。
規約：元の loop 四角形と実比較を保持する。
使われ方：実構造辺の可逆性と π 比較。 -/
theorem dgKappaNativeBFLoopInverseEdge_hom :
    Truncated.HomotopyCategory.homMk
      (dgKappaNativeBFLoopInverseEdge R D I hBF hcofinal Z hS) =
        (OmegaSpectrum.nativeLoopVertexIso
          (dgKappaNativeBFLoopSquare R D I hBF hcofinal Z hS)).inv :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ _)

/-- 概要：同じ未完備実核 K から同じ実商の native loop への実 fibration 辺。
方針：元の実 loop 逆辺の始点だけを同じ実核の指定頂点へ戻す。
規約：採用済み供給と未完備全 S• fibration に条件付き。
使われ方：既存の固定 K 構造辺の利用側に元の実 fibration 辺を供給する。 -/
def dgKappaNativeBFFibrationEdge : Sp.{max (u + 1) v}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeKernelCategory R D I))))
    ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))))) :=
  (SSet.Edge.ofTruncated (dgKappaNativeBFLoopInverseEdge R D I hBF hcofinal Z hS)).ofEq
    (dgKappaNativeBFSquare_source R D I hBF) rfl

/-- 概要：同じ未完備実 fibration 辺は元の実 loop 同型の逆として可逆。
方針：代表辺の元の同型性を、全一単体を保つ始点の照合で移す。
規約：完備化後の固定 K の構造辺の可逆性は主張しない。
使われ方：固定 K へ完備化を続ける前の実比較。 -/
theorem dgKappaNativeBFFibrationEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (dgKappaNativeBFFibrationEdge R D I hBF hcofinal Z hS).toTruncated := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (dgKappaNativeBFLoopInverseEdge R D I hBF hcofinal Z hS) := by
    change IsIso (Truncated.HomotopyCategory.homMk
      (dgKappaNativeBFLoopInverseEdge R D I hBF hcofinal Z hS))
    rw [dgKappaNativeBFLoopInverseEdge_hom]
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (dgKappaNativeBFFibrationEdge R D I hBF hcofinal Z hS).toTruncated)
    (f := dgKappaNativeBFLoopInverseEdge R D I hBF hcofinal Z hS) rfl).mpr he

/-- 概要：同じ未完備実 fibration 辺は全整数 π 同型。
方針：元の実可逆辺を同じ π 関手に写す。
規約：未完備全 S• fibration 等に条件付き。完備化後の全整数同型は結論しない。
使われ方：固定 K への完備化を合成した後の非負次数比較。 -/
theorem dgKappaNativeBFFibrationEdge_pi_bijective (j : ℤ) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaNativeBFFibrationEdge R D I hBF hcofinal Z hS).toTruncated) j) := by
  have := dgKappaNativeBFFibrationEdge_isInvertible R D I hBF hcofinal Z hS
  exact ConcreteCategory.bijective_of_isIso
    ((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk
      (dgKappaNativeBFFibrationEdge R D I hBF hcofinal Z hS).toTruncated))

/-- 概要：同じ有限 BF 四角形から得る元の固定 K の実構造辺。
方針：同じ実 fibration 辺を既存の元の P・Yoneda 比較の間に置く。
規約：固定 S・ν・K と同じ I を保持し、別の fibration 辺は仮定しない。
使われ方：K-7 c5 の元の反復列の実構造辺。 -/
def dgKappaNativeBFFixedStructureEdge :=
  dgKappaNativeStructureEdge R D I
    (dgKappaNativeBFFibrationEdge R D I hBF hcofinal Z hS)

/-- 概要：同じ有限 BF 四角形からの元の固定 K 構造射は非負次数 π 同型。
方針：実未完備比較と同じ元の Yoneda 完備化比較を既存の利用側で合成する。
規約：有限 BF・共終性・全 S• fibration に条件付き。K₀ 全射性は要求しない。
使われ方：K-7 d3 の元の実隣接安定化への接続。 -/
theorem dgKappaNativeBFFixedStructureMap_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaNativeStructureMap R D I
      (dgKappaNativeBFFibrationEdge R D I hBF hcofinal Z hS)) j) :=
  dgKappaNativeStructureMap_nonnegative R D I _ hcofinal
    (fun k _ => dgKappaNativeBFFibrationEdge_pi_bijective R D I hBF hcofinal Z hS k) j hj

end SerrePositivity.KST.NonConnective
