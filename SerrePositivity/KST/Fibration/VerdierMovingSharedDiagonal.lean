module
public import SerrePositivity.KST.Fibration.VerdierNativeDiagonalCoordinates
public import SerrePositivity.KST.Fibration.VerdierReadoutMovingLongInput
public import SerrePositivity.KST.Fibration.VerdierMovingUpperNativeEndpoints
public import SerrePositivity.KST.Fibration.VerdierMovingUpperShortEndpoints
public import SerrePositivity.KST.Fibration.VerdierLowerSuppliedNormalization

/-!
概要：元の動く全 S• 第二短辺を保持した上下二胞体族を、全共有対角で貼る。
方針：同じ下側読出しと同じ全 S• 比較の相対合成を実上側 encoder へ渡す。
規約：供給命題引数と厳密切断を使わず、元の下側との可逆比較を保持する。
使われ方：K-6 c4 の指定有限端点照合へ渡す、動く実上側全族。
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

/-- 概要：同じ実下側の正規化と動く実上側族を、同じ全共有対角で接続する。
方針：元の下側読出しを固定境界付きで合成し、その同じ実長 Hom を再構成する。
規約：上側第二短辺を定値へ置き換えず、全一単体の比較と同じ両端の全 native Hom を保持する。
使われ方：残る指定有限端点・同じ三面内比較を行うための実上下族。 -/
theorem verdierMovingSharedDiagonal_nativeEndpoints_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ∃ (N F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierFullSLowerDeformation d).h N) ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ N =
        fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ F = verdierMovingUpperHorn d ∧
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ N =
        (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ F ∧
      HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (verdierOriginalNativeHomFamily d 0)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F
            (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) ∧
      HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const
          (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
          (verdierNativeCompositePoint d 1)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F
            (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  obtain ⟨N, L, hN, hNhorn, hNdiag, hL, hread⟩ :=
    verdierLowerNormalizedReconstruction_supplied d
  have hRec := verdierLowerNormalizedReadout_recovery d L hread
  obtain ⟨H, T, hT⟩ := verdierReadoutRelativeComposition_exists d L hRec hL
  let ℓ := verdierReadoutMovingLongInput d L hRec hL H T hT
  let F := verdierMovingUpperFamily d ℓ
  refine ⟨N, F, hN, hNhorn, verdierMovingUpperFamily_horn d ℓ, ?_,
    verdierMovingUpperFamily_first_native d L hRec hL H T hT,
    verdierMovingUpperFamily_last_native d L hRec hL H T hT⟩
  let direct : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} :=
    { I := {ULift.up 0, ULift.up 2}
      left := by simp
      right := by simp
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  have hDirect : coherentTriangleDirectPath.{u} = direct := by
    apply SimplicialThickening.Path.ext
    ext ⟨a⟩
    fin_cases a <;> simp [coherentTriangleDirectPath, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath, direct] <;> decide
  have hlow : verdierLowerNativeLongHomTransport d Δ[1] L ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct)) =
      (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct))) ≫
        eqToHom (verdierLowerNativeLongHomTarget_eq d) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  have hF := verdierMovingUpperFamily_diagonal d ℓ
  have hd := verdierReadoutMovingLongInput_direct d L hRec hL H T hT
  rw [hDirect] at hF hd
  have hlower := hNdiag.trans (verdierLowerNativeDiagonal_transport d Δ[1]
    (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct))))
  exact hlower.trans ((congrArg (verdierNativeDiagonalFamily d Δ[1])
    (hd.trans hlow).symm).trans hF.symm)

/-- 概要：同じ実下側と動く上側全族を、全共有対角で接続する既存の公開形。
方針：同じ実両端の全 native Hom も持つ強化存在定理を特殊化する。
規約：既存の公開型を保持。使われ方：元の全四角形比較への利用側。 -/
theorem verdierMovingSharedDiagonal_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ∃ (N F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierFullSLowerDeformation d).h N) ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ N =
        fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ F = verdierMovingUpperHorn d ∧
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ N =
        (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ F := by
  obtain ⟨N, F, hN, hNhorn, hFhorn, hdiag, _, _⟩ :=
    verdierMovingSharedDiagonal_nativeEndpoints_exists d
  exact ⟨N, F, hN, hNhorn, hFhorn, hdiag⟩

end SerrePositivity.KST.Fibration
