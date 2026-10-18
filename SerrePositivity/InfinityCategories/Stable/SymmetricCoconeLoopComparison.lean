module
public import SerrePositivity.InfinityCategories.Stable.SymmetricCoconeKernelPair

/-! # 対称 span 全体の余錐空間とループ模型

概要：始対象へ向かう辺を二度使う span の余錐空間は、共通始点の余錐空間のループ模型と同値。
方針：全体の余錐空間の自己引き戻し表示と、可縮な枝のループ比較を合成する。
規約：比較は基点の選択を含む。使われ方：二枝交換をループの逆射へ移すための空間の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：辺の終点の始対象性はその Yoneda 表示での終点にも成り立つ。
方針：辺の終点への制限の式を Yoneda 同値で読む。
規約：値域の quasicategory 性は不要。使われ方：枝の可縮性の入力を指定終点で与える。 -/
lemma stableEdgeSimplex_target_initial {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : IsInitialVertex z) :
    IsInitialVertex (SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) := by
  have h := congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) (edgeSimplex_target f)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm ▸ hz

/-- 概要：対称 span の全体の余錐空間から共通始点の余錐空間のループ模型への比較。
方針：自己引き戻しの同型を枝の自己引き戻しのループ比較へ合成する。
規約：指定辺の終点の始対象性と枝の余錐の基点を使う。使われ方：交換作用のループ表示。 -/
def symmetricCoconeLoopComparison {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : IsInitialVertex z)
    (y : X _⦋0⦌) (e : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    coconeMappingSpace (edgeSpan f f) y ⟶
      pinchedHomLeft ((coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y).app (Opposite.op ⦋0⦌) e)
        ((coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y).app (Opposite.op ⦋0⦌) e) :=
  (symmetricCoconeKernelPairIso f y).hom ≫ coconeBranchKernelPairLoopComparison
    (SSet.yonedaEquiv.symm f.edge) (stableEdgeSimplex_target_initial f hz) y e

/-- 概要：対称 span 全体の余錐空間のループ比較は単体的ホモトピー同値。
方針：自己引き戻しとの同型とループ比較の同値性を合成する。
規約：X の安定性全体は不要。使われ方：Hom 表示と基点付きループ模型の空間そのものの比較。 -/
lemma symmetricCoconeLoopComparison_homotopyEquivalence
    {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : IsInitialVertex z)
    (y : X _⦋0⦌) (e : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (symmetricCoconeLoopComparison f hz y e) := by
  have h₁ := (qCatEquivalenceOfIso (symmetricCoconeKernelPairIso f y)).isQCatEquivalence
  have h₂ := (coconeBranchKernelPairLoopComparison_homotopyEquivalence
    (SSet.yonedaEquiv.symm f.edge) (stableEdgeSimplex_target_initial f hz) y e).isQCatEquivalence
  exact (h₁.comp h₂).isSimplicialHomotopyEquivalence

/-- 概要：対称 span の余錐空間の連結成分は共通始点余錐空間の基点の自己射と同値。
方針：自己引き戻しとの同型の π₀ と枝のループの Hom 同値を合成する。
規約：群構造との両立はこの定義だけでは主張しない。使われ方：二枝交換の逆射との比較。 -/
def symmetricCoconePiZeroLoopEquiv {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : IsInitialVertex z)
    (y : X _⦋0⦌) (e : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    SSet.π₀ (coconeMappingSpace (edgeSpan f f) y) ≃
      ((SSet.HomotopyCategory.mk
        ((coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y).app (Opposite.op ⦋0⦌) e) :
          hoFunctor.obj (coconeMappingSpace
            (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge) y)) ⟶
        SSet.HomotopyCategory.mk
          ((coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y).app (Opposite.op ⦋0⦌) e)) :=
  (SSet.π₀Functor.mapIso (symmetricCoconeKernelPairIso f y)).toEquiv.trans
    (coconeBranchKernelPairPiZeroLoopEquiv (SSet.yonedaEquiv.symm f.edge)
      (stableEdgeSimplex_target_initial f hz) y e)

/-- 概要：対称 span の π₀ の同値は実際のループ比較の π₀ への作用と一致する。
方針：比較射の合成と連結成分の合成の計算則を読む。
規約：固定した枝の基点を使う。使われ方：空間の比較と通常の射の照合。 -/
lemma symmetricCoconePiZeroLoopEquiv_eq_comparison
    {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : IsInitialVertex z)
    (y : X _⦋0⦌) (e : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (coconeMappingSpace (edgeSpan f f) y)) :
    symmetricCoconePiZeroLoopEquiv f hz y e a =
      pinchedHomLeftPiZeroEquiv _ _ (SSet.mapπ₀ (symmetricCoconeLoopComparison f hz y e) a) := by
  change pinchedHomLeftPiZeroEquiv _ _ (SSet.mapπ₀
    (coconeBranchKernelPairLoopComparison (SSet.yonedaEquiv.symm f.edge)
      (stableEdgeSimplex_target_initial f hz) y e)
    (SSet.mapπ₀ (symmetricCoconeKernelPairIso f y).hom a)) = _
  rw [symmetricCoconeLoopComparison, SSet.mapπ₀_comp_apply]

end SerrePositivity.InfinityCategories
