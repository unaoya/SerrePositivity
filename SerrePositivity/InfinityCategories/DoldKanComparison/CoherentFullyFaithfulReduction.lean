module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentHomRetraction
public import SerrePositivity.InfinityCategories.DoldKanComparison.PinchedEndpointTransport

/-!
# 比較写像の充満忠実性と固定端点の比較射

概要：比較写像の Core の充満忠実性を、二つの dg 対象の固定端点の比較射へ帰着する。
方針：実際の pinchedHomMap と端点の等式による移送を同定し、全頂点の再構成を使う。
規約：実際の単体的ホモトピー逆の存在を双方で要求する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9 の写像空間の証明から A3e への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：固定端点の比較射は Core の pinchedHomMap の端点移送に等しい。
方針：全次数で台の単体への作用を比較し、端点の移送で台が変わらないことを使う。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon 2.5.9 の計算した比較射を Core の充満忠実性の射へ同定する。 -/
lemma coherentPinchedComparison_eq_pinchedHomMap (x y : D) :
    coherentPinchedComparison (R := R) x y =
      pinchedHomMap (coherentComparison (R := R) (D := D)) (coherentVertex x) (coherentVertex y) ≫
        (pinchedEndpointIso (coherentComparison_vertex x) (coherentComparison_vertex y)).hom := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply PinchedHom.Simplex.ext
  exact (pinchedEndpointIso_hom_val (coherentComparison_vertex x) (coherentComparison_vertex y)
    (pinchedSimplexMap coherentComparison s)).symm

/-- 概要：固定端点の比較射のホモトピー同値性は Core の対応する射のものと同値である。
方針：比較射の同定後に、端点の等式による移送の不変性を使う。
規約：π₀ の全単射への弱めは行わない。
使われ方：HA 1.3.1.17 の pinched Hom のホモトピー逆を Core に渡す。 -/
lemma coherentPinchedComparison_homotopyEquivalence_iff (x y : D) :
    IsSimplicialHomotopyEquivalence (coherentPinchedComparison (R := R) x y) ↔
      IsSimplicialHomotopyEquivalence (pinchedHomMap (coherentComparison (R := R) (D := D))
        (coherentVertex x) (coherentVertex y)) := by
  rw [coherentPinchedComparison_eq_pinchedHomMap]
  exact pinchedEndpointIso_postcomp_iff _ _ _

/-- 概要：比較写像の充満忠実性は全 dg 対象間の固定端点の比較射のホモトピー同値性と同値。
方針：全 coherent 頂点をその対象から再構成し、端点移送の不変性を使う。
規約：右辺も実際の単体的ホモトピー逆を要求し、追加の整合性仮定はない。
使われ方：Kerodon 2.5.9 の残る写像空間の証明の正確な到達点。 -/
lemma coherentComparison_fullyFaithful_iff :
    IsFullyFaithful (coherentComparison (R := R) (D := D)) ↔
      ∀ x y : D, IsSimplicialHomotopyEquivalence (coherentPinchedComparison (R := R) x y) := by
  constructor
  · intro h x y
    exact (coherentPinchedComparison_homotopyEquivalence_iff x y).mpr (h _ _)
  · intro h s t
    obtain ⟨x, hx⟩ := (coherentVertexEquiv (R := R) (D := D)).symm.surjective s
    obtain ⟨y, hy⟩ := (coherentVertexEquiv (R := R) (D := D)).symm.surjective t
    have hst := (coherentPinchedComparison_homotopyEquivalence_iff (R := R) (D := D) x y).mp
      (h x y)
    change IsSimplicialHomotopyEquivalence (pinchedHomMap
      (coherentComparison (R := R) (D := D)) ((coherentVertexEquiv (R := R) (D := D)).symm x)
        ((coherentVertexEquiv (R := R) (D := D)).symm y)) at hst
    rw [hx, hy] at hst
    exact hst

end SerrePositivity.InfinityCategories.DoldKanComparison
