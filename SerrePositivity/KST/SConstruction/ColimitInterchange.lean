module
public import SerrePositivity.KST.SConstruction.DoubleCoconeUniversality
public import SerrePositivity.KST.SConstruction.FunctorColimitReindex
public import SerrePositivity.KST.SConstruction.ColimitDiagramTransport
public import SerrePositivity.InfinityCategories.Stable.PastingRightCocone

/-! # 二方向の余極限の交換
概要：点ごとの外側余極限は、内側の余極限性を境界から錐頂点へ延長する。
方針：逆順の普遍補完を選び、共通の二重図式上の相対始対象として比較する。
規約：完成した全頂点での内側余極限の存在を明示する。使われ方：gapped 図式の cofiber 閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：点ごとの外側余極限の完成後も内側の普遍性は保たれる。
方針：逆順に補完した二重余錐と相対始対象の一意性で比較する。
規約：完成後の全行に内側余極限が存在することを仮定する。
使われ方：零脚 span の場合に安定性から存在を供給する。 -/
lemma colimitInterchange_initialBoundary {J K C : SSet.{u}} [Quasicategory C]
    (F : join J (Δ[0] : SSet.{u}) ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C)
    (houter : IsPointwiseColimitCone (⟨F, rfl⟩ : JoinCocone (joinInl J Δ[0] ≫ F)))
    (hinner : ∀ j : J _⦋0⦌, InitialBoundaryLifting (coconeRestriction K C)
      ((joinInl J Δ[0] ≫ F).app (Opposite.op ⦋0⦌) j))
    (hex : ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      HasColimit ((functorVertexEquiv K C).symm
        ((F ≫ coconeRestriction K C).app (Opposite.op ⦋0⦌) j))) :
    ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      InitialBoundaryLifting (coconeRestriction K C) (F.app (Opposite.op ⦋0⦌) j) := by
  obtain ⟨H, hH⟩ := exists_colimitCoconeFamily (F ≫ coconeRestriction K C) hex
  let G := H ≫ (relativeInitialVertices (coconeRestriction K C)).ι
  have hG : G ≫ coconeRestriction K C = F ≫ coconeRestriction K C := hH
  have hGi (j : (join J (Δ[0] : SSet.{u})) _⦋0⦌) :
      InitialBoundaryLifting (coconeRestriction K C) (G.app (Opposite.op ⦋0⦌) j) :=
    fullSubcomplexOnVertices_vertex (H.app (Opposite.op ⦋0⦌) j)
  let cF : JoinCocone (joinInl J Δ[0] ≫ F) := ⟨F, rfl⟩
  have hp : HasPointwiseColimits (joinInl J Δ[0] ≫ F) := fun k ↦
    ⟨evaluateFunctorCocone cF k, houter k⟩
  have hFr := isColimitCone_reindex_of_hasPointwiseColimits hp cF
    (isColimitCone_of_pointwise cF houter) (joinInl K (Δ[0] : SSet.{u}))
  have hGo : IsColimitCone (⟨G ≫ coconeRestriction K C, rfl⟩ :
      JoinCocone (joinInl J Δ[0] ≫ G ≫ coconeRestriction K C)) := by
    let dG : JoinCocone (joinInl J Δ[0] ≫ G ≫ coconeRestriction K C) :=
      ⟨G ≫ coconeRestriction K C, rfl⟩
    have hval : (reindexFunctorCocone cF (joinInl K Δ[0])).val = dG.val := hG.symm
    exact (isColimitCone_iff_of_val_eq _ dG hval).1 hFr
  have hFu := doubleCocone_initial_outer_inner F (isColimitCone_of_pointwise cF houter) hinner
  have hGu := doubleCocone_initial_inner_outer G hGi hGo
  have he : (doubleCoconeRestriction J K C).app (Opposite.op ⦋0⦌) (functorVertex F) =
      (doubleCoconeRestriction J K C).app (Opposite.op ⦋0⦌) (functorVertex G) := by
    change functorVertex ((joinInl J Δ[0] ≫ F) ≫ coconeRestriction K C) =
      functorVertex ((joinInl J Δ[0] ≫ G) ≫ coconeRestriction K C)
    simp only [Category.assoc]
    rw [hG]
  let e := doubleCoconeUniversalIso F G hFu hGu he
  intro j
  have ej := VertexIso.map e (evaluateFunctorAt j)
  rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex] at ej
  exact InitialBoundaryLifting.of_vertexIso (coconeRestriction K C) (hGi j) ej.symm

end SerrePositivity.KST.SConstruction
