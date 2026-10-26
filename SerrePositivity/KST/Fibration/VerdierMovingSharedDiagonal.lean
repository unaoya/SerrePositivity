module
public import SerrePositivity.KST.Fibration.VerdierNativeDiagonalCoordinates
public import SerrePositivity.KST.Fibration.VerdierReadoutMovingLongInput
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
規約：上側第二短辺を定値へ置き換えず、全一単体の比較を保持する。
使われ方：残る指定有限端点・同じ三面内比較を行うための実上下族。 -/
theorem verdierMovingSharedDiagonal_exists (d : VerdierDiagram.{u}) :
    ∃ (N F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}),
      Nonempty (FunctorIso (verdierFullSLowerDeformation d).h N) ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ N =
        fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ F = verdierMovingUpperHorn d ∧
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ N =
        (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ F := by
  obtain ⟨N, L, hN, hNhorn, hNdiag, hL, hread⟩ :=
    verdierLowerNormalizedReconstruction_supplied d
  have hRec := verdierLowerNormalizedReadout_recovery d L hread
  obtain ⟨H, T, hT⟩ := verdierReadoutRelativeComposition_exists d L hRec hL
  let ℓ := verdierReadoutMovingLongInput d L hRec hL H T hT
  let F := verdierMovingUpperFamily d ℓ
  refine ⟨N, F, hN, hNhorn, verdierMovingUpperFamily_horn d ℓ, ?_⟩
  let direct : TriangleNativePath.{u} :=
    { I := {ULift.up 0, ULift.up 2}
      left := by simp
      right := by simp
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  have hDirect : coherentTriangleDirectPath.{u} = direct := by
    apply SimplicialThickening.Path.ext
    ext ⟨a⟩
    fin_cases a <;> simp [coherentTriangleDirectPath, coherentOnePath, direct] <;> decide
  have hlow : verdierLowerNativeLongHomTransport d Δ[1] L ≫
      evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct)) =
      (L ≫ evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct))) ≫
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
    (L ≫ evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct))))
  exact hlower.trans ((congrArg (verdierNativeDiagonalFamily d Δ[1])
    (hd.trans hlow).symm).trans hF.symm)

end SerrePositivity.KST.Fibration
