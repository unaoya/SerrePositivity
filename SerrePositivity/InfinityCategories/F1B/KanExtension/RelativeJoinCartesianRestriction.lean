module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.CartesianPreservation
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinInvertingRestriction

/-!
概要：相対 join の図式の族を左包含で制限するとすべての cartesian 辺を保存する。
方針：終点指定の可逆化する持ち上げを選び、比較三角形により一般の cartesian 辺へ拡張する。
規約：底と標的は quasicategory、元の射は cocartesian fibration。
使われ方：fiber ごとの余錐の始対象性を全空間の制限の充填性へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対 join の左包含による相対指数の制限は cartesian 辺を保存する。
方針：可逆化する図式の特殊な輸送を保存することと、終点指定の比較の定理を使う。
規約：底 C と値域 D は quasicategory。
使われ方：Kerodon Lemma 7.3.4.5–6 の cartesian 輸送との両立。 -/
lemma kanRelativeJoinRestriction_preservesCartesianEdges {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (e : (SerrePositivity.InfinityCategories.fiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D) _⦋1⦌)
    (he : IsCartesianEdge (SerrePositivity.InfinityCategories.fiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D) e) :
    IsCartesianEdge (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D)
      ((SerrePositivity.InfinityCategories.fiberwiseHomPre (kanRelativeJoinInlOver p)).app (Opposite.op ⦋1⦌) e) := by
  apply SerrePositivity.InfinityCategories.F1B.cartesianEdges_preserved_of_target_lifts
    (SerrePositivity.InfinityCategories.fiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D)
    (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D) (SerrePositivity.InfinityCategories.fiberwiseHomPre (kanRelativeJoinInlOver p)) ?_ e he
  intro x b hb
  let r := relativeJoinBaseProjection p (𝟙 C)
  let a : (Δ[0] : SSet.{u}) ⟶ SerrePositivity.InfinityCategories.fiberwiseHom r D := SSet.yonedaEquiv.symm x
  let sq : CommSq a (stdSimplex.δ (0 : Fin 2)) (SerrePositivity.InfinityCategories.fiberwiseHomProjection r D) b :=
    ⟨by simpa only [a, SSet.yonedaEquiv_symm_comp] using hb.symm⟩
  let H₀ := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) r ((stdSimplex.δ (0 : Fin 2)) ≫ b)).symm
    ⟨a, sq.w⟩
  obtain ⟨H, hH, hHi⟩ := exists_kanFiberwiseHom_target_extension_inverting r b H₀
  refine ⟨SerrePositivity.InfinityCategories.fiberwiseHomCurry r b H, ?_, SerrePositivity.InfinityCategories.fiberwiseHomCurry_projection r b H, ?_, ?_⟩
  · rw [← SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp, hH]
    exact congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) r _).apply_symm_apply ⟨a, sq.w⟩)
  · exact SerrePositivity.InfinityCategories.fiberwiseHom_isCartesianEdge_of_inverting r _
      (SerrePositivity.InfinityCategories.fiberwiseHomInvertingEdge_of_diagram r b H hHi)
  · rw [SSet.yonedaEquiv_comp]
    exact kanRelativeJoinCurry_pre_isCartesianEdge (D := D) p b H hHi

end SerrePositivity.InfinityCategories.F1B
