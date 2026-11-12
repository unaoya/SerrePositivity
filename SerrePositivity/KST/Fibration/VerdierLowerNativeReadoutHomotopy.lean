module
public import SerrePositivity.KST.Fibration.VerdierLowerNativeReadoutCoordinates

/-!
概要：同じ実下側読出しを、元の下側全 path から実合成端定値族への全ホモトピーへ戻す。
方針：同じ読出しの区間辺を取り、実両端の回収式で端点だけを読み替える。
規約：元の全読出しを保持し、別のホモトピーを選ばない。
使われ方：K-6 c4 の元の上側全 path 比較と実下側読出しの合成。
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

/-- 概要：元の実下側読出しが各入力点の全 native Hom を回収する条件。
方針：実供給の既存回収式を同じ型で保持する。
規約：新たな存在仮定は加えない。
使われ方：実読出し・正規化読出しの両方を同じ全ホモトピーへ渡す。 -/
abbrev VerdierLowerNativeReadoutRecovery (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d)) : Prop :=
  ∀ k : (Δ[1] : SSet.{u + 1}) _⦋0⦌,
    HEq (L.app (Opposite.op ⦋0⦌) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k)).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))

/-- 概要：実供給の下側読出しは同じ各点 native Hom 回収条件を満たす。
方針：実読出しの存在定理を同じ型で消費する。
規約：(9) 全体の存在は使わない。
使われ方：指定両端を持つ実下側ホモトピーの無条件入力。 -/
theorem verdierLowerNativeReadoutRecovery_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ∃ L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d),
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierLowerReconstructionCompositeFamily d Δ[1] ∧
      VerdierLowerNativeReadoutRecovery d L :=
  verdierLowerNativeReadout_exists d

/-- 概要：採用済み正規化仕様の同じ実読出し回収式を、実ホモトピーの入力へ渡す。
方針：curry の頂点と元の族の同じパラメータ制限を照合する。
規約：同じ L を保持し、別の読出し族を選ばない。
使われ方：(9) の normalize(t) と元の実下側との比較を接続する。 -/
theorem verdierLowerNormalizedReadout_recovery (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
    (hL : ∀ k : (Δ[1] : SSet.{u + 1}) _⦋0⦌,
      let s := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
        ((curry (verdierFullSLowerDeformation d).h).app (Opposite.op ⦋0⦌) k))
      HEq (L.app (Opposite.op ⦋0⦌) k)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) :
    VerdierLowerNativeReadoutRecovery d L := by
  intro k
  have hk : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
      ((curry (verdierFullSLowerDeformation d).h).app (Opposite.op ⦋0⦌) k) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.curry_app_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _
  have h := hL k
  dsimp only at h
  rw [hk] at h
  exact h

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)

/-- 概要：同じ実下側読出しから元の下側全 path と定値実合成端を結ぶ全ホモトピー。
方針：同じ区間写像の実辺を両端回収で輸送し、そのまま uncurry する。
規約：元の全読出し・直接端・合成端を保持する。
使われ方：K-6 c4 の境界付き全長 Hom 比較の合成。 -/
def verdierLowerNativeReadoutHomotopy : SSet.Homotopy
    ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 1))
    (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
      (verdierNativeCompositePoint d 1)) := by
  let q := verdierLowerNativeLongHomTransport d Δ[1] L
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.map ((truncation 2).map q)
  let e' := (SSet.Edge.ofTruncated e).ofEq
    (verdierLowerNativeReadoutCoordinates_first d L (hL _))
    (verdierLowerNativeReadoutCoordinates_last d L (hL _))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e'.toTruncated

/-- 概要：同じ全ホモトピーの実写像は元の指定両端へ輸送した読出しの uncurry。
方針：同じ区間辺の恒等一単体表示と Yoneda の往復を回収する。
規約：各頂点だけでなく全パラメータで厳密に元の読出しへ戻る。
使われ方：元の全族を固定したまま境界合成三角形を持ち上げる。 -/
theorem verdierLowerNativeReadoutHomotopy_h :
    (verdierLowerNativeReadoutHomotopy d L hL).h =
      uncurry (verdierLowerNativeLongHomTransport d Δ[1] L) := by
  change uncurry (SSet.yonedaEquiv.symm
    ((verdierLowerNativeLongHomTransport d Δ[1] L).app (Opposite.op ⦋1⦌)
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) = _
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) := by
    apply SSet.stdSimplex.ext
    intro a
    fin_cases a <;> rfl
  rw [hi, ← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.symm_apply_apply]

/-- 概要：同じ読出しの実合成端条件は、全ホモトピーの合成 path 上の全時刻定値性。
方針：同じ uncurry 回収を評価と照合し、元の全族合成端等式を代入する。
規約：同じ L の全時刻条件を保持する。終端一点だけの条件へ弱めない。
使われ方：指定境界合成二単体の終点側の単位条件。 -/
theorem verdierLowerNativeReadoutHomotopy_full
    (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierLowerReconstructionCompositeFamily d Δ[1]) :
    lift (SSet.const (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})))
      (𝟙 (Δ[1] : SSet.{u + 1})) ≫ (verdierLowerNativeReadoutHomotopy d L hL).h =
      SSet.const (verdierNativeCompositePoint d 1) := by
  rw [verdierLowerNativeReadoutHomotopy_h]
  have hshape : lift (SSet.const (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})))
      (𝟙 (Δ[1] : SSet.{u + 1})) ≫
        uncurry (verdierLowerNativeLongHomTransport d Δ[1] L) =
      verdierLowerNativeLongHomTransport d Δ[1] L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  rw [hshape]
  exact verdierLowerNativeLongHomTransport_full d Δ[1] L hfull

end SerrePositivity.KST.Fibration
