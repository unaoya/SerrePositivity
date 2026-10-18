module
public import SerrePositivity.InfinityCategories.Stable.FinalHornRestrictionLifting
public import SerrePositivity.InfinityCategories.F1.CartesianEdge

/-! # 余錐の制限射に対する cartesian な辺

概要：余錐の頂点で可逆な関手の辺は、余錐の制限射に対して cartesian である。
方針：二変数を交換し、相対骨格の最後の頂点での可逆性による外側ホーン充填を使う。
規約：F1 の既存 IsCartesianEdge を用いる。使われ方：S3 の余錐の輸送の認証。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：余錐全体からの関手を余錐の頂点で評価する。
方針：右の零単体の包含を通じて関手を評価する。
規約：X と K は任意の単体集合。
使われ方：Kerodon §5.3.7 の cartesian な余錐の辺の条件。 -/
def coconeApexEvaluation (K X : SSet.{u}) : (ihom (join K (Δ[0] : SSet.{u}))).obj X ⟶ X :=
  evaluateFunctorAt ((joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

/-- 概要：余錐の頂点で可逆な関手の辺は余錐の制限に対して cartesian。
方針：ホーンと余錐の二変数を交換し、余錐の頂点で可逆な最後の辺を用いて相対骨格を充填する。
規約：X は quasicategory、K に有限性や quasicategory 性は仮定しない。
使われ方：Kerodon Proposition 5.3.7.5・7.1.6.13 の余錐の制限の輸送。 -/
lemma isCartesianEdge_coconeRestriction_of_apex {K X : SSet.{u}} [Quasicategory X]
    {f g : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌}
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (join K (Δ[0] : SSet.{u}))).obj X)) f g)
    (he : IsInvertibleEdge (e.map ((truncation 2).map (coconeApexEvaluation K X)))) :
    IsCartesianEdge (coconeRestriction K X) e.edge := by
  intro m σ β hσ sq
  have hw := sq.w
  let D := join K (Δ[0] : SSet.{u})
  let a := internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X β
  let b := internalHomFlipHomEquiv (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) D X σ
  have hsq : a ≫ (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X = joinInl K Δ[0] ≫ b := by
    have hh := congrArg
      (internalHomFlipHomEquiv (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) K X) hw
    rw [coconeRestriction, internalHomFlipHomEquiv_pre_app, internalHomFlipHomEquiv_pre] at hh
    exact hh.symm
  have ht (n : ℕ) (s : D _⦋n⦌)
      (hs : s ∉ Set.range ((joinInl K (Δ[0] : SSet.{u})).app (Opposite.op ⦋n⦌))) :
      IsInvertibleEdge (edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (finalHornEdge m, PinchedHom.constant (simplexLastVertex s) 1))) := by
    have hv : simplexLastVertex s =
        (joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
      unfold simplexLastVertex
      rw [SSet.yonedaEquiv_symm_app]
      exact coconeSimplex_lastVertex_of_not_range s hs
    have hedge : (uncurry b).app (Opposite.op ⦋1⦌)
        (finalHornEdge m, PinchedHom.constant (simplexLastVertex s) 1) =
        (e.map ((truncation 2).map (coconeApexEvaluation K X))).edge := by
      rw [hv]
      dsimp [b, internalHomFlipHomEquiv]
      rw [uncurry_curry]
      change (coconeApexEvaluation K X).app (Opposite.op ⦋1⦌)
        (σ.app (Opposite.op ⦋1⦌) (finalHornEdge m)) = _
      rw [hσ]
      rfl
    exact (isInvertibleEdge_congr hedge).2 he
  obtain ⟨F, hF₁, hF₂⟩ := finalHornRestriction_lift_of_last_vertices (joinInl K Δ[0]) m a b hsq ht
  let G := (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).symm F
  have hG : internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X G = F :=
    (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).apply_symm_apply F
  refine CommSq.HasLift.mk' { l := G, fac_left := ?_, fac_right := ?_ }
  · apply (internalHomFlipHomEquiv (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) D X).injective
    rw [internalHomFlipHomEquiv_pre, hG]
    exact hF₂
  · apply (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X).injective
    change internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X
      (G ≫ (pre (joinInl K (Δ[0] : SSet.{u}))).app X) = _
    rw [internalHomFlipHomEquiv_pre_app, hG]
    exact hF₁


end SerrePositivity.InfinityCategories
