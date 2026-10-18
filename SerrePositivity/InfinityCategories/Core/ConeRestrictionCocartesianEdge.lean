module

public import SerrePositivity.InfinityCategories.Core.InitialHornRestrictionLifting
public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.Core.CocartesianFibration

/-!
概要：錐の制限に対して錐の頂点で可逆な関手の辺は cocartesian。
方針：二変数を交換し、右因子外の単体の最初の頂点が錐の頂点になることと相対骨格の充填を使う。
規約：添字は任意、値域は quasicategory。
使われ方：Kerodon Proposition 5.3.7.5・7.1.6.13 の錐の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：錐全体からの関手を錐の頂点で評価する。
方針：左の零単体の包含を通じて関手を評価する。
規約：X と K は任意の単体集合。
使われ方：Kerodon §5.3.7 の cocartesian な錐の辺の条件。 -/
def coneApexEvaluation (K X : SSet.{u}) : (ihom (join (Δ[0] : SSet.{u}) K)).obj X ⟶ X :=
  evaluateFunctorAt ((joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

/-- 概要：錐の頂点で可逆な関手の辺は錐の制限に対して cocartesian。
方針：ホーンと錐の二変数を交換し、錐の頂点で可逆な最初の辺を用いて相対骨格を充填する。
規約：X は quasicategory、K に有限性や quasicategory 性は仮定しない。
使われ方：Kerodon Proposition 5.3.7.5・7.1.6.13 の錐の制限の輸送。 -/
lemma hasCocartesianHornLifting_coneRestriction_of_apex {K X : SSet.{u}} [Quasicategory X]
    {f g : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (join (Δ[0] : SSet.{u}) K)).obj X)) f g)
    (he : IsInvertibleEdge (e.map ((truncation 2).map (coneApexEvaluation K X)))) :
    HasCocartesianHornLifting (coneRestriction K X) e := by
  intro m σ β hσ hw
  let D := join (Δ[0] : SSet.{u}) K
  let a := internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X β
  let b := internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) D X σ
  have hsq : a ≫ (pre (horn (m + 2) 0).ι).app X = joinInr Δ[0] K ≫ b := by
    have hh := congrArg (internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) K X) hw
    rw [coneRestriction, internalHomFlipHomEquiv_pre_app, internalHomFlipHomEquiv_pre] at hh
    exact hh.symm
  have ht (n : ℕ) (s : D _⦋n⦌)
      (hs : s ∉ Set.range ((joinInr (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌))) :
      IsInvertibleEdge (edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (initialHornEdge m, PinchedHom.constant (simplexFirstVertex s) 1))) := by
    have hv : simplexFirstVertex s =
        (joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
      unfold simplexFirstVertex
      rw [SSet.yonedaEquiv_symm_app]
      exact coneSimplex_firstVertex_of_not_range s hs
    have hedge : (uncurry b).app (Opposite.op ⦋1⦌)
        (initialHornEdge m, PinchedHom.constant (simplexFirstVertex s) 1) =
        (e.map ((truncation 2).map (coneApexEvaluation K X))).edge := by
      rw [hv]
      dsimp [b, internalHomFlipHomEquiv]
      rw [uncurry_curry]
      change (coneApexEvaluation K X).app (Opposite.op ⦋1⦌)
        (σ.app (Opposite.op ⦋1⦌) (initialHornEdge m)) = _
      rw [hσ]
      rfl
    exact (isInvertibleEdge_congr hedge).2 he
  obtain ⟨F, hF₁, hF₂⟩ := initialHornRestriction_lift_of_first_vertices (joinInr Δ[0] K) m a b hsq ht
  let G := (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).symm F
  have hG : internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X G = F :=
    (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).apply_symm_apply F
  refine ⟨G, ?_, ?_⟩
  · apply (internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) D X).injective
    rw [internalHomFlipHomEquiv_pre, hG]
    exact hF₂
  · apply (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X).injective
    change internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X
      (G ≫ (pre (joinInr (Δ[0] : SSet.{u}) K)).app X) = _
    rw [internalHomFlipHomEquiv_pre_app, hG]
    exact hF₁

end SerrePositivity.InfinityCategories
