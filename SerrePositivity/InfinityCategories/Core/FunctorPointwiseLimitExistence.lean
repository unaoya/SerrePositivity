module

public import SerrePositivity.InfinityCategories.Core.TerminalVertexLifting
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion

/-!
概要：点ごとの極限の存在から自然な極限錐を構成する。
方針：各頂点で選んだ極限錐を相対終点境界充填によって自然な族へ延長し、二変数を交換して錐へ戻す。
規約：点ごとの錐の選択に自然性は仮定しない。
使われ方：HTT Proposition 5.1.2.2、Kerodon Propositions 7.1.8.3・7.1.8.7 の極限側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：全評価図式が極限を持てば自然な点ごとの極限錐が存在する。
方針：頂点ごとに極限錐を選び、錐の制限の相対終点境界充填で頂点上の選択を自然な族へ延長する。
規約：X は quasicategory、J・K は任意、選んだ錐の自然性は仮定しない。
使われ方：HTT Proposition 5.1.2.2、Kerodon Proposition 7.1.8.7 の極限側。 -/
lemma exists_pointwiseLimitCone {J K X : SSet.{u}} [Quasicategory X]
    (p : J ⟶ (ihom K).obj X) (hp : HasPointwiseLimits p) :
    ∃ c : JoinCone p, IsPointwiseLimitCone c := by
  classical
  choose c hc using hp
  let T := join (Δ[0] : SSet.{u}) J
  let q := internalHomFlipHomEquiv J K X p
  let x : K _⦋0⦌ → ((ihom T).obj X) _⦋0⦌ := fun k ↦ functorVertex (c k).val
  have hx (k : K _⦋0⦌) : (coneRestriction J X).app (Opposite.op ⦋0⦌) (x k) =
      q.app (Opposite.op ⦋0⦌) k := by
    change functorVertex (joinInr Δ[0] J ≫ (c k).val) = _
    rw [(c k).property]
    dsimp only [q]
    rw [internalHomFlipHomEquiv_app_zero]
    rfl
  have ht (k : K _⦋0⦌) : TerminalBoundaryLifting (coneRestriction J X) (x k) :=
    terminalBoundaryLifting_coneRestriction_of_isLimitCone (c k) (hc k)
  obtain ⟨F, hFp, hFv⟩ := exists_lift_of_terminal_vertex_lifts (coneRestriction J X) q x hx ht
  let G := internalHomFlipHomEquiv K T X F
  have hGF : internalHomFlipHomEquiv T K X G = F :=
    (internalHomFlipHomEquiv K T X).left_inv F
  have hG : joinInr (Δ[0] : SSet.{u}) J ≫ G = p := by
    apply (internalHomFlipHomEquiv J K X).injective
    rw [internalHomFlipHomEquiv_pre, hGF]
    exact hFp
  let C : JoinCone p := ⟨G, hG⟩
  refine ⟨C, ?_⟩
  intro k
  have hk := internalHomFlipHomEquiv_app_zero G k
  rw [hGF] at hk
  change F.app (Opposite.op ⦋0⦌) k = functorVertex (evaluateFunctorCone C k).val at hk
  have heq : evaluateFunctorCone C k = c k :=
    Subtype.ext (functorVertex_injective (hk.symm.trans (hFv k)))
  rw [heq]
  exact hc k

/-- 概要：全評価図式が極限を持つ図式は関手 ∞ 圏で極限を持つ。
方針：自然な点ごとの極限錐を構成し、点ごとの極限性による判定を適用する。
規約：X は quasicategory、図式とパラメーターは任意。
使われ方：HTT Proposition 5.1.2.2、Kerodon Proposition 7.1.8.3 の存在の極限側。 -/
lemma hasLimit_of_hasPointwiseLimits {J K X : SSet.{u}} [Quasicategory X]
    (p : J ⟶ (ihom K).obj X) (hp : HasPointwiseLimits p) : HasLimit p := by
  obtain ⟨c, hc⟩ := exists_pointwiseLimitCone p hp
  exact ⟨c, isLimitCone_of_pointwise c hc⟩

/-- 概要：点ごとの極限が存在する図式の極限錐は各点でも極限錐。
方針：自然な点ごとの極限錐を構成し、極限錐の一意性による同型で点ごとの極限性を移す。
規約：存在仮定 HasPointwiseLimits を明示する。
使われ方：HTT Proposition 5.1.2.2、Kerodon Proposition 7.1.8.3 の一意性による逆方向。 -/
lemma isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits {J K X : SSet.{u}}
    [Quasicategory X] {p : J ⟶ (ihom K).obj X} (hp : HasPointwiseLimits p)
    (c : JoinCone p) (hc : IsLimitCone c) : IsPointwiseLimitCone c := by
  obtain ⟨d, hd⟩ := exists_pointwiseLimitCone p hp
  exact hd.of_vertexIso (limitConeIso d c (isLimitCone_of_pointwise d hd) hc)

/-- 概要：点ごとの極限が存在すれば任意の自然な錐の極限性と点ごとの極限性は同値。
方針：点ごとの極限性からの判定と、自然な極限錐の存在・一意性による逆方向を合わせる。
規約：X は quasicategory、J・K は任意、存在仮定は HasPointwiseLimits のみ。
使われ方：HTT Proposition 5.1.2.2、Kerodon Proposition 7.1.8.3 の極限の完全な比較。 -/
lemma isLimitCone_iff_pointwise_of_hasPointwiseLimits {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (hp : HasPointwiseLimits p) (c : JoinCone p) :
    IsLimitCone c ↔ IsPointwiseLimitCone c :=
  ⟨isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits hp c, isLimitCone_of_pointwise c⟩

end SerrePositivity.InfinityCategories
