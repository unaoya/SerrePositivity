module
public import SerrePositivity.KST.Fibration.ZeroMiddleReconstructionSupply
public import SerrePositivity.KST.Fibration.ZeroMiddleControlledTriangleInput
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFaces

/-!
概要：Ind-S (9) の全族再構成を、同じ零中間二胞体の core 始域・全 S• 中間頂点・短辺へ特殊化する。
方針：元の二短辺の定値パラメータ族と実ホーンを固定し、指定長 Hom の空間へ適用する。
規約：供給命題は明示引数で、再構成の存在を無条件には主張しない。
使われ方：K-6 c4 の全 S• 長 Hom を持つ制御上側の準備。
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
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1})

/-- 概要：元の core 包含を第一短辺として同じ全パラメータで固定する。
方針：同じ実 Kan 射の豊穣頂点の定値族を取る。
規約：元の全 S• 長 Hom は、この同じ core 包含で制限してから渡す。
使われ方：指定長 Hom 再構成の第一短辺入力。 -/
def zeroMiddleFullSFirstFamily :
    K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))) :=
  SSet.const (ULift.up (SimplicialCategory.homEquiv'
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩)) (zeroMiddleControlledFirstMap s)))

/-- 概要：元の全 S• 比較と第二短辺の実合成を同じ全パラメータで固定する。
方針：同じ実 Kan 射の豊穣頂点の定値族を取る。
規約：第二短辺を選び直さない。
使われ方：指定長 Hom 再構成の第二短辺入力。 -/
def zeroMiddleFullSLastFamily :
    K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩))) :=
  SSet.const (ULift.up (SimplicialCategory.homEquiv'
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩))
      (zeroMiddleFullSKanComposite s hZ)))

/-- 概要：元の二短辺そのものを持つ全パラメータの実ホーン。
方針：同じ coherent 二辺のホーンを定値族にする。
規約：同境界の別の辺に取り替えない。
使われ方：再構成空間が固定する実境界。 -/
def zeroMiddleFullSReconstructionHorn : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  fst (Λ[2, 1] : SSet.{u + 1}) K ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (zeroMiddleControlledFirstMap s))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (zeroMiddleFullSKanComposite s hZ))

/-- 概要：同じホーンの第一辺は、指定第一短辺族の標準区間像。
方針：元の coherent 豊穣頂点比較を使う。
規約：全パラメータでの厳密等式を保持する。
使われ方：Ind-S (9) の第一境界条件。 -/
theorem zeroMiddleFullSReconstructionHorn_first :
    (horn₂₁.ι₀₁ ▷ K) ≫ zeroMiddleFullSReconstructionHorn s hZ K =
      (Δ[1] ◁ zeroMiddleFullSFirstFamily s K) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))) := by
  rw [zeroMiddleFullSReconstructionHorn, ← Category.assoc, whiskerRight_fst,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_first]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, zeroMiddleFullSFirstFamily,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalMappingUncurry_const_vertex]
  congr 2

/-- 概要：同じホーンの第二辺は、指定第二短辺族の標準区間像。
方針：元の coherent 豊穣頂点比較を使う。
規約：全パラメータでの厳密等式を保持する。
使われ方：Ind-S (9) の第二境界条件。 -/
theorem zeroMiddleFullSReconstructionHorn_last :
    (horn₂₁.ι₁₂ ▷ K) ≫ zeroMiddleFullSReconstructionHorn s hZ K =
      (Δ[1] ◁ zeroMiddleFullSLastFamily s hZ K) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩))) := by
  rw [zeroMiddleFullSReconstructionHorn, ← Category.assoc, whiskerRight_fst,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_last]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, zeroMiddleFullSLastFamily,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalMappingUncurry_const_vertex]
  congr 2

/-- 概要：合成端を元の二短辺の合成に固定する、全長 Hom 族の実空間。
方針：Ind-S (9) と同じ評価 fiber を、同じ core 始域・全 S• 中間頂点・元の二短辺で取る。
規約：空間の頂点の存在はここでは主張しない。
使われ方：全 S• 長 Hom を再構成へ渡す型。 -/
abbrev zeroMiddleFullSReconstructionLongSpace :=
  let P := CategoryTheory.SimplicialThickening.Path
    (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
  let p : P :=
    { I := Set.univ
      left := Set.mem_univ _
      right := Set.mem_univ _
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
  let H := (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))
  let c := lift (zeroMiddleFullSFirstFamily s K) (zeroMiddleFullSLastFamily s hZ K) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1}
      (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))) (SimplicialCategory.sHom
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u}
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom K).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ p))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c)

/-- 概要：元の二短辺を厳密固定する全パラメータ二胞体の実空間。
方針：同じホーン全族への制限 fiber を取る。
規約：長 Hom の指定とは別の実空間として保持する。
使われ方：再構成された制御二胞体族の行先。 -/
abbrev zeroMiddleFullSReconstructionTriangleSpace :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleFullSReconstructionHorn s hZ K))

/-- 概要：再構成の読出しは各指定点で同じ全 native Hom を返す。
方針：Ind-S (9) の読出し条件を、同じ実二胞体と実長 Hom の両空間へ特殊化する。
規約：単なる合成端や Hom のホモトピー類の一致に弱めない。
使われ方：全族の encode・longHom の厳密回収と指定点での比較。 -/
def zeroMiddleFullSReconstructionRecovery
    (longHom : zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
      zeroMiddleFullSReconstructionLongSpace s hZ K) : Prop :=
  let P := CategoryTheory.SimplicialThickening.Path
    (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
  let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
  let H := (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
      (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))
  ∀ (t : (zeroMiddleFullSReconstructionTriangleSpace s hZ K) _⦋0⦌) (k : K _⦋0⦌),
    let Lt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm
      ((longHom.app (Opposite.op ⦋0⦌) t).val)
    let Tt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm t.val
    let st := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
      ((curry Tt).app (Opposite.op ⦋0⦌) k))
    HEq (Lt.app (Opposite.op ⦋0⦌) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (st.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))

/-- 概要：同じ正規化族の直接 path 評価は実共有対角を厳密回収する。
方針：採用済み補足の全一単体式を同じ core 始域・全 S• 中間頂点へ特殊化する。
規約：パラメータの頂点だけの式へ弱めない。供給命題に条件付き。
使われ方：動く共有対角を全時刻で同じ下側へ貼り合わせる。 -/
def zeroMiddleFullSReconstructionDiagonalRecovery
    (encode : zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
      zeroMiddleFullSReconstructionTriangleSpace s hZ K)
    (longHom : zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
      zeroMiddleFullSReconstructionLongSpace s hZ K) : Prop :=
  let P := CategoryTheory.SimplicialThickening.Path
    (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
  let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
  let H := (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
      (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))
  ∀ t : (zeroMiddleFullSReconstructionTriangleSpace s hZ K) _⦋0⦌,
    let direct : P :=
      { I := {ULift.up 0, ULift.up 2}
        left := by simp
        right := by simp
        left_le := fun k _ => Fin.zero_le k.down
        le_right := fun k _ => Fin.le_last k.down }
    let Lt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm
      ((longHom.app (Opposite.op ⦋0⦌) t).val)
    let nt := encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)
    let Tt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm nt.val
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Tt =
      (Δ[1] ◁ (Lt ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct)))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
            (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
            (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))

/-- 概要：元の実二胞体族と同じ読出しを再構成した正規化族の固定ホーン内比較。
方針：同じ encode・longHom による正規化の指定点を同じ fiber 内で比較する。
規約：元の t 自身への厳密対角回収は要求しない。
使われ方：正規化後に共有対角で貼り合わせ、元の族へ可逆比較で戻す。 -/
def zeroMiddleFullSReconstructionNormalizeComparison
    (encode : zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
      zeroMiddleFullSReconstructionTriangleSpace s hZ K)
    (longHom : zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
      zeroMiddleFullSReconstructionLongSpace s hZ K) : Prop :=
  ∀ t : (zeroMiddleFullSReconstructionTriangleSpace s hZ K) _⦋0⦌,
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t
      (encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)))

/-- 概要：供給命題に条件付きで、同じ実長 Hom 空間から制御二胞体空間への切断がある。
方針：同じ core 始域・全 S• 中間頂点と元の二短辺を Ind-S (9) へ代入する。
規約：存在は供給命題の明示引数に条件付き。全族回収・指定点の全 native Hom を保持する。
使われ方：実供給後の全長 Hom の再構成利用側。 -/
theorem zeroMiddleFullSReconstruction_exists (h9 : zeroMiddleControlledTriangleSupply.{u}) :
    ∃ (encode : zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
        zeroMiddleFullSReconstructionTriangleSpace s hZ K)
      (longHom : zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
        zeroMiddleFullSReconstructionLongSpace s hZ K),
      encode ≫ longHom = 𝟙 _ ∧ zeroMiddleFullSReconstructionRecovery s hZ K longHom ∧
        zeroMiddleFullSReconstructionDiagonalRecovery s hZ K encode longHom ∧
        zeroMiddleFullSReconstructionNormalizeComparison s hZ K encode longHom := by
  obtain ⟨encode, longHom, he, hread, hdiag, hnorm, _⟩ := h9
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)) K
    (zeroMiddleFullSFirstFamily s K) (zeroMiddleFullSLastFamily s hZ K)
    (zeroMiddleFullSReconstructionHorn s hZ K)
    (zeroMiddleFullSReconstructionHorn_first s hZ K)
    (zeroMiddleFullSReconstructionHorn_last s hZ K)
  exact ⟨encode, longHom, he, hread, hdiag, hnorm⟩

variable (h9 : zeroMiddleControlledTriangleSupply.{u})

/-- 概要：供給命題に条件付きの同じ長 Hom 全族から二胞体全族への再構成写像。
方針：同じ再構成供給から encode を取り出す。
規約：元の core 始域と全 S• 中間頂点を保持する。
使われ方：指定実長 Hom 入力の制御上側への像。 -/
def zeroMiddleFullSReconstructionEncode :
    zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
      zeroMiddleFullSReconstructionTriangleSpace s hZ K :=
  (zeroMiddleFullSReconstruction_exists s hZ K h9).choose

/-- 概要：同じ再構成データの全長 Hom の読出し写像。
方針：encode と同じ存在命題から対の longHom を取り出す。
規約：別の再構成供給を選び直さない。
使われ方：全族の厳密回収と指定点の全 native Hom の照合。 -/
def zeroMiddleFullSReconstructionRead :
    zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
      zeroMiddleFullSReconstructionLongSpace s hZ K :=
  (zeroMiddleFullSReconstruction_exists s hZ K h9).choose_spec.choose

/-- 概要：同じ再構成と読出しの合成は長 Hom 全族上の恒等そのもの。
方針：同じ供給の切断式を回収する。
規約：点ごとの等式やホモトピー類へ弱めない。
使われ方：同じ実長 Hom 入力の全単体の回収。 -/
theorem zeroMiddleFullSReconstructionEncode_read :
    zeroMiddleFullSReconstructionEncode s hZ K h9 ≫
      zeroMiddleFullSReconstructionRead s hZ K h9 = 𝟙 _ :=
  (zeroMiddleFullSReconstruction_exists s hZ K h9).choose_spec.choose_spec.1

/-- 概要：同じ読出しは全指定点で元の二胞体の全 native Hom と一致する。
方針：encode と同時に得た読出しの回収式を使う。
規約：全族切断式と同じデータに条件付き。
使われ方：制御上側と元の二胞体の全 Hom の照合。 -/
theorem zeroMiddleFullSReconstructionRead_recovery :
    zeroMiddleFullSReconstructionRecovery s hZ K
      (zeroMiddleFullSReconstructionRead s hZ K h9) :=
  (zeroMiddleFullSReconstruction_exists s hZ K h9).choose_spec.choose_spec.2.1

/-- 概要：同じ読出しを再構成した正規化族は共有対角の全一単体を厳密回収する。
方針：encode と同時に得た採用済み対角回収式を使う。
規約：各頂点の全 Hom 一致で代用しない。
使われ方：K-6 c4 の動く共有対角の接続。 -/
theorem zeroMiddleFullSReconstructionRead_diagonal :
    zeroMiddleFullSReconstructionDiagonalRecovery s hZ K
      (zeroMiddleFullSReconstructionEncode s hZ K h9)
      (zeroMiddleFullSReconstructionRead s hZ K h9) :=
  (zeroMiddleFullSReconstruction_exists s hZ K h9).choose_spec.choose_spec.2.2.1

/-- 概要：同じ再構成の正規化は元の族と固定ホーン内で可逆比較される。
方針：同じ供給に付随する正規化比較を取り出す。
規約：Ind-S (9) の正規化後の仕様に条件付き。
使われ方：正規化族で対角を貼り、元の族に戻す。 -/
theorem zeroMiddleFullSReconstructionRead_normalizeComparison :
    zeroMiddleFullSReconstructionNormalizeComparison s hZ K
      (zeroMiddleFullSReconstructionEncode s hZ K h9)
      (zeroMiddleFullSReconstructionRead s hZ K h9) :=
  (zeroMiddleFullSReconstruction_exists s hZ K h9).choose_spec.choose_spec.2.2.2

end SerrePositivity.KST.Fibration
