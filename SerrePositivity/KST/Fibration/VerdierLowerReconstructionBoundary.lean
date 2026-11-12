module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerRelativeDeformation
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSReconstruction

/-!
概要：元の下側全変形を、正規化再構成が要求する同じ二短辺の境界と実入力点へ戻す。
方針：元の native 二辺を厳密回収し、同じ全変形を固定ホーン族の fiber に置く。
規約：元の共有対角は動くまま保持する。再構成供給やその存在は仮定しない。
使われ方：K-6 c4 の実下側族を normalize(t) に渡す前の入力照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：実下側の元の二短辺は同じ回収射の coherent ホーンそのもの。
方針：元の二つの面の一単体を厳密回収する。
規約：対角の合成やホモトピー類だけの比較に弱めない。
使われ方：正規化再構成の二短辺条件への実代入。 -/
theorem verdierFullSLowerHorn_composable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierFullSLowerHorn d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap
        (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (verdierLowerTriangle d)))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap
          (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (verdierLowerTriangle d))))) := by
  apply horn₂₁.isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_first, verdierFullSLowerHorn, ← Category.assoc, horn.ι_ι]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact zeroMiddleCoreSingleKanTriangle_first (verdierLowerTriangle d)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_last, verdierFullSLowerHorn, ← Category.assoc, horn.ι_ι]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact zeroMiddleCoreSingleKanTriangle_last (verdierLowerTriangle d)

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (K : SSet.{u + 1})

/-- 概要：実下側の元の第一短辺を全パラメータで固定する。
方針：同じ回収 Kan 射の豊穣頂点の定値族を取る。
規約：元の native 一単体を選び直さない。
使われ方：Ind-S (9) の実下側への入力境界。 -/
def verdierLowerReconstructionFirstFamily :
    K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom
        (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))) :=
  SSet.const (ULift.up (SimplicialCategory.homEquiv'
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
    (stableCoreSingleKanMap
      (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (verdierLowerTriangle d))))))

/-- 概要：同じ固定ホーンの第一辺は指定短辺族の標準区間像。
方針：元の coherent ホーンと豊穣頂点の比較を使う。
規約：全パラメータの厳密等式。
使われ方：実下側族への再構成仕様の境界条件。 -/
theorem verdierLowerReconstructionHorn_first :
    (horn₂₁.ι₀₁ ▷ K) ≫
      (fst (Λ[2, 1] : SSet.{u + 1}) K ≫ verdierFullSLowerHorn d) =
        (Δ[1] ◁ verdierLowerReconstructionFirstFamily d K) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
            (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
            (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))) := by
  rw [verdierFullSLowerHorn_composable, ← Category.assoc, whiskerRight_fst,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_first]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, verdierLowerReconstructionFirstFamily,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalMappingUncurry_const_vertex]
  congr 2

/-- 概要：実下側の元の第二短辺を全パラメータで固定する。
方針：同じ回収 Kan 射の豊穣頂点の定値族を取る。
規約：元の native 一単体を選び直さない。
使われ方：Ind-S (9) の実下側への入力境界。 -/
def verdierLowerReconstructionLastFamily :
    K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom
        (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
        (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩))) :=
  SSet.const (ULift.up (SimplicialCategory.homEquiv'
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩))
    (stableCoreSingleKanMap
      (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (verdierLowerTriangle d))))))

/-- 概要：同じ固定ホーンの第二辺は指定短辺族の標準区間像。
方針：元の coherent ホーンと豊穣頂点の比較を使う。
規約：全パラメータの厳密等式。
使われ方：実下側族への再構成仕様の境界条件。 -/
theorem verdierLowerReconstructionHorn_last :
    (horn₂₁.ι₁₂ ▷ K) ≫
      (fst (Λ[2, 1] : SSet.{u + 1}) K ≫ verdierFullSLowerHorn d) =
        (Δ[1] ◁ verdierLowerReconstructionLastFamily d K) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
            (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
            (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩))) := by
  rw [verdierFullSLowerHorn_composable, ← Category.assoc, whiskerRight_fst,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_last]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, verdierLowerReconstructionLastFamily,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalMappingUncurry_const_vertex]
  congr 2

/-- 概要：元の下側二短辺の全族を厳密固定する再構成空間。
方針：同じ実ホーン族への制限の fiber を使う。
規約：上側の中間対象を持つ空間とは区別する。
使われ方：同じ実下側変形を正規化前の点として保持する。 -/
abbrev verdierLowerReconstructionTriangleSpace :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (fst (Λ[2, 1] : SSet.{u + 1}) K ≫ verdierFullSLowerHorn d))

/-- 概要：元の下側全変形そのものは同じ固定ホーン族の実入力点。
方針：元の全変形と実ホーン回収式を関手頂点へ写す。
規約：元の動く共有対角を選び直さず、再構成の存在を仮定しない。
使われ方：normalize(t) と元 t の比較に渡す具体的な元の族。 -/
def verdierLowerReconstructionPoint :
    (verdierLowerReconstructionTriangleSpace d Δ[1]) _⦋0⦌ := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierFullSLowerDeformation d).h, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫
    (verdierFullSLowerDeformation d).h) = _
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierFullSLowerDeformation_horn d)

/-- 概要：同じ実入力点から元の下側全変形が厳密に回収される。
方針：関手頂点の同じ標準順逆比較を使う。
規約：各点だけでなく全三角柱の射を回収する。
使われ方：正規化後の可逆比較を元の実下側族へ戻す。 -/
theorem verdierLowerReconstructionPoint_recovery :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ Δ[1]) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
      (verdierLowerReconstructionPoint d).val = (verdierFullSLowerDeformation d).h :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

/-- 概要：元の下側二短辺の合成を同じ全パラメータで固定する。
方針：同じ豊穣合成と宇宙持ち上げの積比較を使う。
規約：指定二短辺を変えず、再構成の合成端をそのまま保持する。
使われ方：実下側の長 Hom 読出しの全時刻の合成端。 -/
def verdierLowerReconstructionCompositeFamily :=
  lift (verdierLowerReconstructionFirstFamily d K)
    (verdierLowerReconstructionLastFamily d K) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1}
        (SimplicialCategory.sHom
          (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
          (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩)))
        (SimplicialCategory.sHom
          (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
          (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)))).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u}
          (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
          (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
          (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)))

/-- 概要：同じ合成端族は元の二つの実 Kan 射の厳密合成の定値族。
方針：全単体上の元の豊穣作用を計算する。
規約：頂点だけでなく全パラメータの射の等式を使う。
使われ方：上側へ長 Hom 入力を渡す際の実合成端の照合。 -/
theorem verdierLowerReconstructionCompositeFamily_eq :
  let X := stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
  let Z := stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)
  verdierLowerReconstructionCompositeFamily d K =
    SSet.const (ULift.up (SimplicialCategory.homEquiv' X Z
      (stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (verdierLowerTriangle d))) ≫
        stableCoreSingleKanMap
          (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (verdierLowerTriangle d)))))) := by
  dsimp only [verdierLowerReconstructionCompositeFamily]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  rfl

end SerrePositivity.KST.Fibration
