module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLimitConeExistence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackConeComponentCriterion
public import SerrePositivity.InfinityCategories.Core.TerminalTransport

/-!
概要：両入力の極限の存在と保存から lax pullback の極限の存在と成分判定を得る。
方針：両成分を保つ極限錐を構成し、一意性の同型を元の射影で写す。
規約：保存性は元の p・q と実際の入力図式についてだけ仮定する。
使われ方：有限極限と射影の極限保存の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

variable {J A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
variable (p : A ⟶ C) (q : B ⟶ C) (r : J ⟶ laxPullback p q)
variable (ha : HasLimit (r ≫ laxPullbackFst p q)) (hb : HasLimit (r ≫ laxPullbackSnd p q))
variable (hp : ∀ c : JoinCone (r ≫ laxPullbackFst p q),
  IsLimitCone c → IsLimitCone (mapJoinCone p c))
variable (hq : ∀ c : JoinCone (r ≫ laxPullbackSnd p q),
  IsLimitCone c → IsLimitCone (mapJoinCone q c))
include ha hb hp hq

/-- 概要：入力に極限が存在し元の二関手が保てば lax pullback の図式は極限を持つ。
方針：入力の極限錐を選び、両成分を保つ全体の極限錐を構成する。
規約：保存性に全図式の保存は要求しない。
使われ方：Tamme Lemma 8 の有限極限の存在。 -/
lemma hasLimit_laxPullback_of_components : HasLimit r := by
  obtain ⟨ca, hca⟩ := ha
  obtain ⟨cb, hcb⟩ := hb
  obtain ⟨c, hc, _, _⟩ := exists_limitCone_laxPullback_with_components p q r ca cb
    hca hcb (hp ca hca) (hq cb hcb)
  exact ⟨c, hc⟩

/-- 概要：存在と保存の仮定の下で、lax pullback の極限性は両入力の極限性と同値。
方針：構成した極限錐と元の極限錐の同型を両射影で写し、逆方向は成分の十分条件を使う。
規約：元の指定錐 c の両射影を判定する。
使われ方：射影の極限保存と成分ごとの極限計算。 -/
lemma isLimitCone_laxPullback_iff_components (c : JoinCone r) :
    IsLimitCone c ↔ IsLimitCone (mapJoinCone (laxPullbackFst p q) c) ∧
      IsLimitCone (mapJoinCone (laxPullbackSnd p q) c) := by
  constructor
  · intro hc
    obtain ⟨ca, hca⟩ := ha
    obtain ⟨cb, hcb⟩ := hb
    obtain ⟨d, hd, hda, hdb⟩ := exists_limitCone_laxPullback_with_components p q r ca cb
      hca hcb (hp ca hca) (hq cb hcb)
    let e := limitConeIso d c hd hc
    have hdal : IsLimitCone (mapJoinCone (laxPullbackFst p q) d) := hda.symm ▸ hca
    have hdbl : IsLimitCone (mapJoinCone (laxPullbackSnd p q) d) := hdb.symm ▸ hcb
    exact ⟨hdal.of_vertexIso (VertexIso.map e (sliceOverPostcomp r (laxPullbackFst p q))),
      hdbl.of_vertexIso (VertexIso.map e (sliceOverPostcomp r (laxPullbackSnd p q)))⟩
  · rintro ⟨hca, hcb⟩
    exact isLimitCone_laxPullback_of_components p q c hca hcb (hp _ hca) (hq _ hcb)

end SerrePositivity.InfinityCategories.F2
