module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFConeZero

/-!
概要：実供給 BF 四角形の fiber と同じ cone の零性から実構造辺を作る。
方針：元の実錐比較に、同じ実 loop 比較同型の逆辺を後合成する。
規約：新 BF 四対象を保持し、旧固定 K との実頂点同型は仮定しない。
使われ方：K-7 c5・d3 の実供給側の構造辺と非負次数比較。
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
local instance suppliedBFConnectiveCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance suppliedBFConnectiveHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ実錐比較の標的は元の実 fiber の指定頂点。
方針：元の錐四角形の左下評価と同じ錐頂点の回収式を使う。
規約：同じ実極限錐を保持する。
使われ方：実比較辺の標的の厳密照合。 -/
theorem dgKappaSuppliedBFFiberComparison_target :
    (dgKappaSuppliedBFKLimitCone R D I).vertex =
      (dgKappaSuppliedBFCanonicalFiberSquare R D I).fiber := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (dgKappaSuppliedBFKLimitCone R D I))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_sourceEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgKappaNativeCoherentBFSquare R D I)))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{max (u + 1) v})
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{max (u + 1) v + 1}) ⊗ Δ[1])) 0 0)).app
    (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap _).app (Opposite.op ⦋0⦌)
      (dgKappaSuppliedBFKLimitCone R D I)) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_vertex] at h
  exact h.symm

/-- 概要：同じ実 fiber 四角形の右辺は元の実供給右辺そのもの。
方針：同じ FiberSquare の境界回収式を使う。
規約：旧 BF 右辺に取り替えない。
使われ方：実供給の同じ商頂点・cone 頂点を回収する。 -/
private theorem suppliedBFCanonicalFiber_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgKappaSuppliedBFCanonicalFiberSquare R D I).square =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgKappaNativeCoherentBFSquare R D I := by
  rw [(dgKappaSuppliedBFCanonicalFiberSquare R D I).right_edge, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
  exact SSet.yonedaEquiv.symm_apply_apply _

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : DGKappaZeroInput R D I)

/-- 概要：同じ実 fiber は同じ未完備実商の新 BF 模型の loop 四角形。
方針：元の右辺・零角を保つ実極限錐と同じ実 cone の K 零性を使う。
規約：共終性に条件付き。元の BF 四角形の引き戻し性は仮定しない。
使われ方：元の実 fiber 比較を同じ未完備実商の loop へ送る。 -/
def dgKappaSuppliedBFConnectiveLoopSquare :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 1) where
  toZeroTriangle := (dgKappaSuppliedBFCanonicalFiberSquare R D I).toZeroTriangle
  target_eq := by
    have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSuppliedBFCanonicalFiberSquare R D I).square 1 1 =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 1 := by
      rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target, suppliedBFCanonicalFiber_right, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target]
    exact ht
  other_zero := by
    have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSuppliedBFCanonicalFiberSquare R D I).square 1 0 =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 0 := by
      rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source, suppliedBFCanonicalFiber_right, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source]
    rw [hs]
    exact dgKappaSuppliedBFSquare_middle_isZero R D I hcofinal Z
  isPullback := (dgKappaSuppliedBFCanonicalFiberSquare R D I).isPullback

/-- 概要：同じ実 fiber の loop 比較同型の逆を表す元の実辺。
方針：同じ Sp 正本の比較同型の逆の代表辺を取る。
規約：全 S• や固定 K の Sp 引き戻し性は仮定しない。
使われ方：元の実未完備比較に後合成する可逆辺。 -/
def dgKappaSuppliedBFConnectiveLoopInverseEdge :
    Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (dgKappaSuppliedBFConnectiveLoopSquare R D I hcofinal Z).vertex
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 1)) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (OmegaSpectrum.nativeLoopVertexIso
      (dgKappaSuppliedBFConnectiveLoopSquare R D I hcofinal Z)).inv)

/-- 概要：同じ元の逆比較辺は実 loop 比較同型の逆を表す。
方針：同じ代表辺の選択仕様を回収する。
規約：元の実 fiber と同じ比較同型を保持する。
使われ方：同じ実構造辺の非負次数判定。 -/
theorem dgKappaSuppliedBFConnectiveLoopInverseEdge_hom :
    Truncated.HomotopyCategory.homMk
      (dgKappaSuppliedBFConnectiveLoopInverseEdge R D I hcofinal Z) =
        (OmegaSpectrum.nativeLoopVertexIso
          (dgKappaSuppliedBFConnectiveLoopSquare R D I hcofinal Z)).inv :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ _)

/-- 概要：元の実 fiber 比較を経る、同じ未完備実核の新 BF 模型から実商の新 BF loop への実辺。
方針：同じ全比較辺に同じ実 loop 比較同型の逆辺を後合成する。
規約：別の fibration 辺の存在は仮定しない。
使われ方：固定 K への元の完備化比較の前の実辺。 -/
def dgKappaSuppliedBFConnectiveFibrationEdge : Sp.{max (u + 1) v}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgKappaNativeCoherentBFSquare R D I)).vertex
    ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 1)) :=
  SSet.Edge.ofTruncated
    ((SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)).ofEq
        rfl (dgKappaSuppliedBFFiberComparison_target R D I) |>.toTruncated.comp
      (dgKappaSuppliedBFConnectiveLoopInverseEdge R D I hcofinal Z))

/-- 概要：一回の S• fibration に条件付きで、同じ実未完備構造辺は非負次数 π 同型。
方針：同じ実 fiber 比較の非負次数同型と元の実 loop 同型を合成する。
規約：全段の Sp 引き戻し性や零次全射性は要求しない。
使われ方：K-7 c5・d3 の連結主経路の隣接安定化。 -/
theorem dgKappaSuppliedBFConnectiveFibrationEdge_nonnegative
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaSuppliedBFConnectiveFibrationEdge R D I hcofinal Z).toTruncated) j) := by
  let a := ((SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)).ofEq
    rfl (dgKappaSuppliedBFFiberComparison_target R D I)).toTruncated
  let b := dgKappaSuppliedBFConnectiveLoopInverseEdge R D I hcofinal Z
  have hb : IsIso (Truncated.HomotopyCategory.homMk b) := by
    rw [show Truncated.HomotopyCategory.homMk b = _ from
      dgKappaSuppliedBFConnectiveLoopInverseEdge_hom R D I hcofinal Z]
    infer_instance
  have hbj : Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk b) j) :=
    ConcreteCategory.bijective_of_isIso ((SpectrumHo.piFunctor j).map
      (Truncated.HomotopyCategory.homMk b))
  change Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk (a.comp b)) j)
  rw [← Truncated.HomotopyCategory.homMk_comp_homMk (a.compStruct b), SpectrumHo.piMap_comp]
  have hcast : ∀ (x y y' : Sp.{max (u + 1) v} _⦋0⦌)
      (e : Sp.Edge x y) (hy : y = y'),
      Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk e.toTruncated) j) →
        Function.Bijective (SpectrumHo.piMap
          (Truncated.HomotopyCategory.homMk (e.ofEq rfl hy).toTruncated) j) := by
    intro x y y' e hy he
    subst y'
    exact he
  exact hbj.comp (hcast _ _ _ _ (dgKappaSuppliedBFFiberComparison_target R D I)
    (dgKappaSuppliedBFFiberComparison_nonnegative R D I hS j hj))


end SerrePositivity.KST.NonConnective
