module
public import SerrePositivity.KST.Fibration.VerdierNativeDiagonalCoordinates
public import SerrePositivity.KST.Fibration.ZeroMiddleCanonicalEncoder
public import SerrePositivity.KST.Fibration.VerdierLowerSuppliedNormalization

/-!
概要：同じ実下側の正規化と実上側の再構成を、全時刻で同じ共有対角へ接続する。
方針：下側読出しを元の合成端比較で移し、正規化側の直接 path 回収式を使う。
規約：供給命題引数と厳密切断は使わない。指定上側有限端点の照合は別工程。
使われ方：K-6 c4 の動く共有対角の貼り合わせと残る有限端点照合の分離。
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

/-- 概要：実下側に可逆比較される正規化族と、同じ全対角を持つ実全 S• 上側族が得られる。
方針：同じ実読出しの直接端を全族で保ち、両側の正規化対角回収を共通座標へ戻す。
規約：全ホーンと元の下側との可逆比較を保持し、実 canonical encoder を消費する。
使われ方：K-6 c4 の指定有限端点・縦辺の照合へ渡す共有対角付きの上下全族。 -/
theorem verdierCanonicalSharedDiagonal_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ∃ (N F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierFullSLowerDeformation d).h N) ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ N =
        fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ F =
        zeroMiddleFullSReconstructionHorn (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d) Δ[1] ∧
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ N =
        (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ F := by
  obtain ⟨N, L, hN, hNhorn, hNdiag, hL, _⟩ :=
    verdierLowerNormalizedReconstruction_supplied d
  let q := verdierLowerNativeLongHomTransport d Δ[1] L
  have hq := verdierLowerNativeLongHomTransport_full d Δ[1] L hL
  let U := verdierNativeLongHomShiftFamily d Δ[1] q hq
  have hU := verdierNativeLongHomShiftFamily_full d Δ[1] q hq
  let Uraw := verdierUpperNativeLongHomTransport d Δ[1] U
  have hUraw := verdierUpperNativeLongHomTransport_full d Δ[1] U hU
  let s := verdierUpperTriangle d
  let hZ := verdierUpperTriangle_middle_isZero d
  let ℓ : (zeroMiddleFullSReconstructionLongSpace s hZ Δ[1]) _⦋0⦌ := by
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex Uraw, ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (Uraw ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex _
    apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    refine hUraw.trans ?_
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  let F := zeroMiddleCanonicalFamily s hZ Δ[1] ℓ
  refine ⟨N, F, hN, hNhorn, zeroMiddleCanonicalFamily_horn s hZ Δ[1] ℓ, ?_⟩
  let direct : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} :=
    { I := {ULift.up 0, ULift.up 2}
      left := by simp
      right := by simp
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  let ev := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := (SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})) (Y := verdierNativeLongHomTarget d)
    (ULift.up (ComposableArrows.mk₀ direct))
  have hlow : q ≫ ev = (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ direct))) ≫
        eqToHom (verdierLowerNativeLongHomTarget_eq d) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  have hupp : Uraw ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct)) =
      (U ≫ ev) ≫ eqToHom (verdierUpperNativeLongHomTarget_eq d).symm := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  have hDirect : coherentTriangleDirectPath.{u} = direct := by
    apply SimplicialThickening.Path.ext
    ext ⟨a⟩
    fin_cases a <;> simp [coherentTriangleDirectPath, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath, direct] <;> decide
  have hFdiag := zeroMiddleCanonicalFamily_diagonal s hZ Δ[1] ℓ
  rw [hDirect] at hFdiag
  have hraw : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ℓ.val = Uraw :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply Uraw
  change (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ F =
    (Δ[1] ◁ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ℓ.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ direct)))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩))) at hFdiag
  rw [hraw, hupp] at hFdiag
  have hupper := hFdiag.trans (verdierUpperNativeDiagonal_transport d Δ[1] (U ≫ ev))
  have hlower := hNdiag.trans (verdierLowerNativeDiagonal_transport d Δ[1]
    (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct))))
  exact hlower.trans ((congrArg (verdierNativeDiagonalFamily d Δ[1]) hlow.symm).trans
    ((congrArg (verdierNativeDiagonalFamily d Δ[1])
      (verdierNativeLongHomShiftFamily_direct d Δ[1] q hq).symm).trans hupper.symm))

end SerrePositivity.KST.Fibration
