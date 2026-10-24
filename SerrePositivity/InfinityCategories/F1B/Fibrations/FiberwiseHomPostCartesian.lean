module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseHomPostcomposition
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CartesianPreservation
public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseHomCartesianFibration

/-!
概要：標的への後合成は変動する関手の全空間の cartesian 輸送を保つ。
方針：cocartesian 辺を可逆にする特殊な輸送を選び、その保存から一般の辺へ移す。
規約：標的の射 U には充填性を要求しない。
使われ方：相対 Kan 比較が底方向の輸送を保つことの第二成分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：可逆化する図式の後合成も可逆化する図式を与える。
方針：curry の後合成の自然性と可逆辺の関手による保存を使う。
規約：図式のパラメータは底の任意の辺。
使われ方：特殊な cartesian 輸送の後合成による保存。 -/
lemma fiberwiseHomPostcomp_inverting_of_diagram {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E) (b : (Δ[1] : SSet.{u}) ⟶ C)
    (H : pullback b p ⟶ D)
    (hH : ∀ s : (pullback b p) _⦋1⦌, IsCocartesianEdge (pullback.fst b p) s →
      IsInvertibleEdge (edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s))) :
    SerrePositivity.InfinityCategories.FiberwiseHomInvertingEdge p E
      (SSet.yonedaEquiv (SerrePositivity.InfinityCategories.fiberwiseHomCurry p b H ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p U)) := by
  rw [← SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp]
  apply SerrePositivity.InfinityCategories.fiberwiseHomInvertingEdge_of_diagram
  intro s hs
  exact (isInvertibleEdge_congr (show
    ((edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s)).map ((truncation 2).map U)).edge =
      (edgeOfSimplex ((H ≫ U).app (Opposite.op ⦋1⦌) s)).edge from rfl)).1 ((hH s hs).map U)

/-- 概要：標的への後合成は関手の全空間の cartesian 辺を保存する。
方針：終点を指定した可逆化する図式の延長を選び、比較三角形で一般の辺へ拡張する。
規約：底と両標的は quasicategory、元の射影は cocartesian fibration。
使われ方：相対 Kan 拡張の全空間の比較と底方向の輸送との両立。 -/
lemma fiberwiseHomPostcomp_preservesCartesianEdges {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E)
    (e : (SerrePositivity.InfinityCategories.fiberwiseHom p D) _⦋1⦌)
    (he : IsCartesianEdge (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D) e) :
    IsCartesianEdge (SerrePositivity.InfinityCategories.fiberwiseHomProjection p E)
      ((SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p U).app (Opposite.op ⦋1⦌) e) := by
  apply SerrePositivity.InfinityCategories.F1B.cartesianEdges_preserved_of_target_lifts
    (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D) (SerrePositivity.InfinityCategories.fiberwiseHomProjection p E)
    (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p U) ?_ e he
  intro x b hb
  let a : (Δ[0] : SSet.{u}) ⟶ SerrePositivity.InfinityCategories.fiberwiseHom p D := SSet.yonedaEquiv.symm x
  let sq : CommSq a (stdSimplex.δ (0 : Fin 2)) (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D) b :=
    ⟨by simpa only [a, SSet.yonedaEquiv_symm_comp] using hb.symm⟩
  let H₀ := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) p ((stdSimplex.δ (0 : Fin 2)) ≫ b)).symm
    ⟨a, sq.w⟩
  obtain ⟨H, hH, hHi⟩ := exists_kanFiberwiseHom_target_extension_inverting p b H₀
  refine ⟨SerrePositivity.InfinityCategories.fiberwiseHomCurry p b H, ?_, SerrePositivity.InfinityCategories.fiberwiseHomCurry_projection p b H, ?_, ?_⟩
  · rw [← SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp, hH]
    exact congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) p _).apply_symm_apply ⟨a, sq.w⟩)
  · exact SerrePositivity.InfinityCategories.fiberwiseHom_isCartesianEdge_of_inverting p _
      (SerrePositivity.InfinityCategories.fiberwiseHomInvertingEdge_of_diagram p b H hHi)
  · exact SerrePositivity.InfinityCategories.fiberwiseHom_isCartesianEdge_of_inverting p _
      (fiberwiseHomPostcomp_inverting_of_diagram p U b H hHi)

end SerrePositivity.InfinityCategories.F1B
