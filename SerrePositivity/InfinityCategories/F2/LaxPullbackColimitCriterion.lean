module

public import SerrePositivity.InfinityCategories.F2.LaxPullbackColimitConeExistence
public import SerrePositivity.InfinityCategories.F2.LaxPullbackCoconeComponentCriterion
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-!
概要：両入力の余極限の存在と保存から lax pullback の余極限の存在と成分判定を得る。
方針：両成分を保つ余極限錐を構成し、一意性の同型を元の射影で写す。
規約：保存性は元の p・q と実際の入力図式についてだけ仮定する。
使われ方：有限余極限と射影の余極限保存の接続。
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
variable (ha : HasColimit (r ≫ laxPullbackFst p q)) (hb : HasColimit (r ≫ laxPullbackSnd p q))
variable (hp : ∀ c : JoinCocone (r ≫ laxPullbackFst p q),
  IsColimitCone c → IsColimitCone (F1B.kanPostcomposeCocone p c))
variable (hq : ∀ c : JoinCocone (r ≫ laxPullbackSnd p q),
  IsColimitCone c → IsColimitCone (F1B.kanPostcomposeCocone q c))
include ha hb hp hq

/-- 概要：入力に余極限が存在し元の二関手が保てば lax pullback の図式は余極限を持つ。
方針：入力の余極限錐を選び、両成分を保つ全体の余極限錐を構成する。
規約：保存性に全図式の保存は要求しない。
使われ方：Tamme Lemma 8 の有限余極限の存在。 -/
lemma hasColimit_laxPullback_of_components : HasColimit r := by
  obtain ⟨ca, hca⟩ := ha
  obtain ⟨cb, hcb⟩ := hb
  obtain ⟨c, hc, _, _⟩ := exists_colimitCone_laxPullback_with_components p q r ca cb
    hca hcb (hp ca hca) (hq cb hcb)
  exact ⟨c, hc⟩

/-- 概要：存在と保存の仮定の下で、lax pullback の余極限性は両入力の余極限性と同値。
方針：構成した余極限錐と元の余極限錐の同型を両射影で写し、逆方向は成分の十分条件を使う。
規約：元の指定余錐 c の両射影を判定する。
使われ方：射影の余極限保存と成分ごとの余極限計算。 -/
lemma isColimitCone_laxPullback_iff_components (c : JoinCocone r) :
    IsColimitCone c ↔ IsColimitCone (F1B.kanPostcomposeCocone (laxPullbackFst p q) c) ∧
      IsColimitCone (F1B.kanPostcomposeCocone (laxPullbackSnd p q) c) := by
  constructor
  · intro hc
    obtain ⟨ca, hca⟩ := ha
    obtain ⟨cb, hcb⟩ := hb
    obtain ⟨d, hd, hda, hdb⟩ := exists_colimitCone_laxPullback_with_components p q r ca cb
      hca hcb (hp ca hca) (hq cb hcb)
    let e := colimitConeIso d c hd hc
    have hdal : IsColimitCone (F1B.kanPostcomposeCocone (laxPullbackFst p q) d) := hda.symm ▸ hca
    have hdbl : IsColimitCone (F1B.kanPostcomposeCocone (laxPullbackSnd p q) d) := hdb.symm ▸ hcb
    exact ⟨hdal.of_vertexIso (VertexIso.map e (sliceUnderPostcomp r (laxPullbackFst p q))),
      hdbl.of_vertexIso (VertexIso.map e (sliceUnderPostcomp r (laxPullbackSnd p q)))⟩
  · rintro ⟨hca, hcb⟩
    exact isColimitCone_laxPullback_of_components p q c hca hcb (hp _ hca) (hq _ hcb)

end SerrePositivity.InfinityCategories.F2
