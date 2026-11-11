module
public import SerrePositivity.KST.SConstruction.ColimitInterchange
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCompletion

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
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm (((pre i).app C).app (Opposite.op ⦋0⦌) v) =
      i ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).surjective v
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C) (i ≫ F)) =
    i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C) F)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- 概要：四角形の押し出し性は span の錐の相対始対象性と同値。
方針：関手頂点で表した正方形を実際の射へ戻す。
規約：C は quasicategory。使われ方：余極限交換の正方形への適用。 -/
lemma squareDiagram_pushout_iff_initialBoundary {C : SSet.{u}} [Quasicategory C]
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (horn 2 0 : SSet.{u}) C)
        (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom).app C).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C) F)) ↔ _
  rw [Equiv.symm_apply_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_initialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)

/-- 概要：点ごとの余極限を取った後も押し出し四角形の普遍性は保たれる。
方針：正方形を span の錐に直し、逆順の普遍補完との比較を使う。
規約：完成後の全 span に余極限が存在するという前提を明記する。
使われ方：零脚の場合は安定性が存在を供給する。 -/
lemma pushoutInterchange {J C : SSet.{u}} [Quasicategory C]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
    (houter : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone (⟨F, rfl⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ F)))
    (hinner : ∀ j : J _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ F).app (Opposite.op ⦋0⦌) j)))
    (hex : ∀ j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (F.app (Opposite.op ⦋0⦌) j)))) :
    ∀ j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (F.app (Opposite.op ⦋0⦌) j)) := by
  let B := F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom).app C
  have hBo : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone (⟨B, rfl⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ B)) :=
    houter.reindex _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom
  have hBi (j : J _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (horn 2 0 : SSet.{u}) C)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ B).app (Opposite.op ⦋0⦌) j) :=
    (squareDiagram_pushout_iff_initialBoundary _).1 (hinner j)
  have hbase : B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (horn 2 0 : SSet.{u}) C =
      F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C := by
    dsimp only [B, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction]
    rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
    rfl
  have hBx (j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) C).symm
        ((B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (horn 2 0 : SSet.{u}) C).app (Opposite.op ⦋0⦌) j)) := by
    rw [hbase]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) C).symm
      (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C).app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) j)))
    rw [squareDiagram_pre]
    exact hex j
  have hi := colimitInterchange_initialBoundary B hBo hBi hBx
  intro j
  exact (squareDiagram_pushout_iff_initialBoundary _).2 (hi j)

end SerrePositivity.KST.SConstruction
