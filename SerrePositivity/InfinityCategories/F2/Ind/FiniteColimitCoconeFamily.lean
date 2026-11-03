module
public import SerrePositivity.InfinityCategories.Core.FiniteLimitsColimits

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteYonedaColimitPreservation
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeConeFamilies

/-!
概要：元の有限 C 図式の全族を、Ind Yoneda も保存する余極限余錐の全族へ延長する。
方針：普遍余錐の射影の切断で同じ全パラメーターを保ち、各値に有限余極限保存を適用する。
規約：有限交換は明示入力。頂点ごとの独立した選択に置き換えない。
使われ方：単一 filtered 表示の同じ添字上で有限余極限を組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 概要：指定全族の制限を厳密に固定した有限余極限余錐族があり、各値を Ind Yoneda が保存。
方針：同じ普遍余錐族の切断。規約：元の全パラメーター。
使われ方：有限形状の単一 filtered 表示から有限余極限を作る。 -/
lemma exists_indYoneda_finiteColimit_coconeFamily (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {A K C : SSet.{u}} [K.Finite] [Quasicategory C] [HasFiniteColimits C]
    (a : A ⟶ (ihom K).obj C) :
    ∃ l : A ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C,
      l ≫ coconeRestriction K C = a ∧ ∀ x : A _⦋0⦌,
        IsColimitCone (kanCoconeFamilyAt l x) ∧
        IsColimitCone (mapJoinCocone (indYoneda κ C)
          (JoinCocone.ulift.{u, u + 1} (kanCoconeFamilyAt l x))) := by
  obtain ⟨s, hs⟩ := exists_colimitCoconeFamily a
    (fun x ↦ HasFiniteColimits.hasColimit ((functorVertexEquiv K C).symm
      (a.app (Opposite.op ⦋0⦌) x)))
  let l := s ≫ (relativeInitialVertices (coconeRestriction K C)).ι
  have hl : l ≫ coconeRestriction K C = a := hs
  refine ⟨l, hl, fun x ↦ ?_⟩
  have h := fullSubcomplexOnVertices_vertex (s.app (Opposite.op ⦋0⦌) x)
  change InitialBoundaryLifting (coconeRestriction K C) (l.app (Opposite.op ⦋0⦌) x) at h
  rw [← kanCoconeFamilyAt_vertex l x] at h
  have hc := isColimitCone_of_initialBoundaryLifting_coconeRestriction
    (kanCoconeFamilyAt l x) h
  exact ⟨hc, indYoneda_finiteColimit_isColimit κ hκ hex _ hc⟩

end SerrePositivity.InfinityCategories.F2.Ind
