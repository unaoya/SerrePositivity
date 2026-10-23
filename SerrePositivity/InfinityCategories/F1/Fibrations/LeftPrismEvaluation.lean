module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftPrismCutCoordinates
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison

/-!
概要：左 Hom の区間比較を、元の coslice 単体の切断制限として計算する。
方針：パラメーターへの自然性と左点 join の標準表示で一般の単体を評価する。
規約：始点もパラメーターも任意。充填性を仮定しない。
使われ方：反転した豊穣 Hom の辺を既存の左区間模型へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 左点 join の任意の図式の prism 評価は、始点を付加した単体の切断制限。 -/
lemma leftMappingSpacePrism_evaluate {A X : SSet.{u}} (F : join Δ[0] A ⟶ X)
    {n : ℕ} (a : A _⦋n⦌) (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    F.app (Opposite.op ⦋n⦌) ((leftMappingSpacePrism A).app (Opposite.op ⦋n⦌) (t, a)) =
      X.map (SimplexCategory.mkHom (coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom)).op
        (SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
          joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm a) ≫ F)) := by
  let f := SSet.yonedaEquiv.symm a
  let g := joinMap (𝟙 Δ[0]) f ≫ F
  let b := (leftMappingSpacePrism Δ[n]).app (Opposite.op ⦋n⦌)
    (t, SSet.yonedaEquiv (𝟙 Δ[n]))
  have hn := congrArg (fun h ↦ h (t, SSet.yonedaEquiv (𝟙 Δ[n])))
    (NatTrans.congr_app (leftMappingSpacePrism_naturality f) (Opposite.op ⦋n⦌))
  change (leftMappingSpacePrism A).app (Opposite.op ⦋n⦌)
      (t, f.app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (𝟙 Δ[n]))) =
    (joinMap (𝟙 Δ[0]) f).app (Opposite.op ⦋n⦌) b at hn
  rw [SSet.yonedaEquiv_symm_app_id] at hn
  rw [hn, ← SSet.yonedaEquiv_symm_app_objEquiv_symm, Equiv.symm_apply_apply]
  change g.app (Opposite.op ⦋n⦌) b = ((leftPointStdSimplexIso n).inv ≫ g).app
    (Opposite.op ⦋n⦌) _
  rw [← leftMappingSpacePrism_stdSimplex_cut n t]
  change g.app (Opposite.op ⦋n⦌) b =
    ((leftPointStdSimplexIso n).hom ≫ (leftPointStdSimplexIso n).inv ≫ g).app
      (Opposite.op ⦋n⦌) b
  rw [Iso.hom_inv_id_assoc]

/-- coslice fiber の族を展開した左点 join の標準単体表示は、元の fiber 単体。 -/
lemma cosliceFiberUncurry_simplex {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)
    {n : ℕ} (a : A _⦋n⦌) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm a) ≫ cosliceFiberUncurry f) =
        cosliceFiberSimplex n (f.app (Opposite.op ⦋n⦌) a) := by
  have h := congrArg (fun g : A ⟶ vertexFiber
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ↦
      (g.app (Opposite.op ⦋n⦌) a).val.val) (cosliceFiberCurry_uncurry f)
  change joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm a) ≫ cosliceFiberUncurry f =
    (f.app (Opposite.op ⦋n⦌) a).val.val at h
  exact congrArg (fun k ↦ SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫ k)) h

/-- coslice fiber の区間比較の評価は、元の単体の左切断による制限。 -/
lemma cosliceFiberToIntervalMappingSpace_evaluate {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)
    {n : ℕ} (a : A _⦋n⦌) (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (intervalMappingUncurry (f ≫ cosliceFiberToIntervalMappingSpace x y)).app
      (Opposite.op ⦋n⦌) (t, a) =
    X.map (SimplexCategory.mkHom (coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom)).op
      (cosliceFiberSimplex n (f.app (Opposite.op ⦋n⦌) a)) := by
  rw [cosliceFiberToIntervalMappingSpace_uncurry]
  change (cosliceFiberUncurry f).app (Opposite.op ⦋n⦌)
    ((leftMappingSpacePrism A).app (Opposite.op ⦋n⦌) (t, a)) = _
  rw [leftMappingSpacePrism_evaluate, cosliceFiberUncurry_simplex]

end SerrePositivity.InfinityCategories
