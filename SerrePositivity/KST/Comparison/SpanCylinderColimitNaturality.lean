module

public import SerrePositivity.KST.Comparison.SpanCylinderColimit

/-!
# 円筒と具体的な余極限の比較の自然性

概要：span とその余極限の可換な比較は、円筒を潰す比較とも可換である。
方針：中央の円筒と左右の頂点で計算し、三部分からの射の一意性を使う。
規約：Segal 1974 Lemma 1.7 の通常の pushout への移送。
使われ方：四頂点の局所化同型によるホモトピー引き戻し性の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel
open scoped Simplicial

/--
概要：円筒から余極限への比較は、span と余錐の可換な比較に対して自然である。
方針：区間を忘れる中央の式と、左右の包含の式を照合する。
規約：余極限の間の射には各構造写像との可換性だけを要求する。
使われ方：通常の付着の各頂点の四角形の比較。
-/
theorem spanCylinderToColimit_naturality {F G : WalkingSpan ⥤ SSet.{u}} (α : F ⟶ G)
    (c : Cocone F) (hc : IsColimit c) (c' : Cocone G) (hc' : IsColimit c')
    (p : c.pt ⟶ c'.pt) (hp : ∀ d, c.ι.app d ≫ p = α.app d ≫ c'.ι.app d) :
    spanCylinderFunctor.map α ≫ spanCylinderToColimit G c' hc' =
      spanCylinderToColimit F c hc ≫ p := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderDesc.doubleMappingCylinder_hom_ext (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
  · let mF := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
    let mG := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle (G.map WalkingSpan.Hom.fst) (G.map WalkingSpan.Hom.snd)
    have hm : mF ≫ spanCylinderFunctor.map α = (α.app .zero ▷ Δ[1]) ≫ mG :=
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map _ _ _ _ _ _ _
        (α.naturality WalkingSpan.Hom.fst).symm (α.naturality WalkingSpan.Hom.snd).symm
    have hw : (α.app .zero ▷ (Δ[1] : SSet.{u})) ≫ fst (G.obj .zero) (Δ[1] : SSet.{u}) =
        fst (F.obj .zero) (Δ[1] : SSet.{u}) ≫ α.app .zero := whiskerRight_fst _ _
    change mF ≫ (spanCylinderFunctor.map α ≫ spanCylinderToColimit G c' hc') =
      mF ≫ (spanCylinderToColimit F c hc ≫ p)
    calc
      _ = (mF ≫ spanCylinderFunctor.map α) ≫ spanCylinderToColimit G c' hc' :=
        (Category.assoc _ _ _).symm
      _ = ((α.app .zero ▷ Δ[1]) ≫ mG) ≫ spanCylinderToColimit G c' hc' := by rw [hm]
      _ = (α.app .zero ▷ Δ[1]) ≫
          (fst (G.obj .zero) (Δ[1] : SSet.{u}) ≫ c'.ι.app .zero) := by
        rw [Category.assoc, spanCylinder_middle_toColimit]
      _ = fst (F.obj .zero) (Δ[1] : SSet.{u}) ≫ (α.app .zero ≫ c'.ι.app .zero) := by
        rw [← Category.assoc, hw, Category.assoc]
      _ = fst (F.obj .zero) (Δ[1] : SSet.{u}) ≫ (c.ι.app .zero ≫ p) :=
        congrArg (fun q => fst (F.obj .zero) (Δ[1] : SSet.{u}) ≫ q) (hp .zero).symm
      _ = (mF ≫ spanCylinderToColimit F c hc) ≫ p := by
        rw [spanCylinder_middle_toColimit, Category.assoc]
      _ = _ := Category.assoc _ _ _
  · change spanCylinderLeft.app F ≫ (spanCylinderFunctor.map α ≫ _) =
      spanCylinderLeft.app F ≫ (_ ≫ p)
    rw [← Category.assoc, ← spanCylinderLeft.naturality α, Category.assoc,
      spanCylinderLeft_toColimit, ← Category.assoc, spanCylinderLeft_toColimit]
    exact (hp .left).symm
  · change spanCylinderRight.app F ≫ (spanCylinderFunctor.map α ≫ _) =
      spanCylinderRight.app F ≫ (_ ≫ p)
    rw [← Category.assoc, ← spanCylinderRight.naturality α, Category.assoc,
      spanCylinderRight_toColimit, ← Category.assoc, spanCylinderRight_toColimit]
    exact (hp .right).symm

/--
概要：単射な右脚の二つの span の成分ごとの局所化同型は、具体的な余極限でも局所化同型となる。
方針：円筒の模型の不変性と、余極限への比較の可逆性から二対三で導く。
規約：余極限の射には構造写像との可換性だけを要求する。
使われ方：境界の有限被覆の比較射の貼り合わせ。
-/
theorem spanColimit_map_localized_isIso {F G : WalkingSpan ⥤ SSet.{u}}
    [Mono (F.map WalkingSpan.Hom.snd)] [Mono (G.map WalkingSpan.Hom.snd)]
    (α : F ⟶ G) (hα : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (α.app d)))
    (c : Cocone F) (hc : IsColimit c) (c' : Cocone G) (hc' : IsColimit c')
    (p : c.pt ⟶ c'.pt) (hp : ∀ d, c.ι.app d ≫ p = α.app d ≫ c'.ι.app d) :
    IsIso (AnodyneHomotopy.anodyneQ.map p) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hF := spanCylinderToColimit_localized_isIso F c hc
  have hG := spanCylinderToColimit_localized_isIso G c' hc'
  have hα' := spanCylinderFunctor_map_localized_isIso α hα
  have hn := spanCylinderToColimit_naturality α c hc c' hc' p hp
  have h : IsIso (Q.map (spanCylinderToColimit F c hc) ≫ Q.map p) := by
    rw [← Q.map_comp, ← hn, Q.map_comp]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp h

end SerrePositivity.KST.Comparison
