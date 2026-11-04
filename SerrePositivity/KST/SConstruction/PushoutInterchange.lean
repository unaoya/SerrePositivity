module
public import SerrePositivity.KST.SConstruction.ColimitInterchange
public import SerrePositivity.InfinityCategories.Stable.PushoutCompletion

/-! # 点ごとの余極限と押し出しの交換
概要：押し出し四角形の族の点ごとの余極限は、必要な span の余極限が存在すれば押し出し。
方針：正方形を span の右錐に直し、二方向の余極限交換を適用する。
規約：完成後の span の存在条件を明記する。使われ方：gapped 図式の点ごとの cofiber 閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：四角形の頂点表示への前合成は元の図式への前合成を表す。
方針：関手頂点の同値の逆律を使う。
規約：始域 A と標的 C は任意。使われ方：span の存在条件の照合。 -/
lemma squareDiagram_pre {A C : SSet.{u}}
    (i : A ⟶ (Δ[1] ⊗ Δ[1] : SSet.{u}))
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌) :
    (functorVertexEquiv A C).symm (((pre i).app C).app (Opposite.op ⦋0⦌) v) =
      i ≫ squareDiagram v := by
  obtain ⟨F, rfl⟩ := (functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).surjective v
  change (functorVertexEquiv A C).symm ((functorVertexEquiv A C) (i ≫ F)) =
    i ≫ (functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).symm
      ((functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C) F)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- 概要：四角形の押し出し性は span の錐の相対始対象性と同値。
方針：関手頂点で表した正方形を実際の射へ戻す。
規約：C は quasicategory。使われ方：余極限交換の正方形への適用。 -/
lemma squareDiagram_pushout_iff_initialBoundary {C : SSet.{u}} [Quasicategory C]
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌) :
    IsPushoutSquare (squareDiagram v) ↔
      InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) C)
        (((pre spanCoconeSquareIso.hom).app C).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨F, rfl⟩ := (functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).surjective v
  change IsPushoutSquare ((functorVertexEquiv _ C).symm ((functorVertexEquiv _ C) F)) ↔ _
  rw [Equiv.symm_apply_apply]
  exact isColimitCone_iff_initialBoundaryLifting (pushoutCocone F)

/-- 概要：点ごとの余極限を取った後も押し出し四角形の普遍性は保たれる。
方針：正方形を span の錐に直し、逆順の普遍補完との比較を使う。
規約：完成後の全 span に余極限が存在するという前提を明記する。
使われ方：零脚の場合は安定性が存在を供給する。 -/
lemma pushoutInterchange {J C : SSet.{u}} [Quasicategory C]
    (F : join J (Δ[0] : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
    (houter : IsPointwiseColimitCone (⟨F, rfl⟩ : JoinCocone (joinInl J Δ[0] ≫ F)))
    (hinner : ∀ j : J _⦋0⦌,
      IsPushoutSquare (squareDiagram ((joinInl J Δ[0] ≫ F).app (Opposite.op ⦋0⦌) j)))
    (hex : ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      HasColimit (pushoutSpan (squareDiagram (F.app (Opposite.op ⦋0⦌) j)))) :
    ∀ j : (join J (Δ[0] : SSet.{u})) _⦋0⦌,
      IsPushoutSquare (squareDiagram (F.app (Opposite.op ⦋0⦌) j)) := by
  let B := F ≫ (pre spanCoconeSquareIso.hom).app C
  have hBo : IsPointwiseColimitCone (⟨B, rfl⟩ : JoinCocone (joinInl J Δ[0] ≫ B)) :=
    houter.reindex spanCoconeSquareIso.hom
  have hBi (j : J _⦋0⦌) : InitialBoundaryLifting
      (coconeRestriction (horn 2 0 : SSet.{u}) C)
      ((joinInl J Δ[0] ≫ B).app (Opposite.op ⦋0⦌) j) :=
    (squareDiagram_pushout_iff_initialBoundary _).1 (hinner j)
  have hbase : B ≫ coconeRestriction (horn 2 0 : SSet.{u}) C =
      F ≫ (pre spanSquareBoundary).app C := by
    dsimp only [B, coconeRestriction]
    rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
    rfl
  have hBx (j : (join J (Δ[0] : SSet.{u})) _⦋0⦌) :
      HasColimit ((functorVertexEquiv (horn 2 0 : SSet.{u}) C).symm
        ((B ≫ coconeRestriction (horn 2 0 : SSet.{u}) C).app (Opposite.op ⦋0⦌) j)) := by
    rw [hbase]
    change HasColimit ((functorVertexEquiv (horn 2 0 : SSet.{u}) C).symm
      (((pre spanSquareBoundary).app C).app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) j)))
    rw [squareDiagram_pre]
    exact hex j
  have hi := colimitInterchange_initialBoundary B hBo hBi hBx
  intro j
  exact (squareDiagram_pushout_iff_initialBoundary _).2 (hi j)

end SerrePositivity.KST.SConstruction
