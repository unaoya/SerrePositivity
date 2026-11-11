module

public import SerrePositivity.KST.Comparison.BasedPathFamily
public import SerrePositivity.KST.Comparison.PointedUnitEvaluation

/-!
# 基点始点 path の族の終点評価

概要：K-L9 の path の終点評価を通常の指数の終点評価と同定し、区間の族を復元する。
方針：点つき単位の非基点評価と、curry・端点への制限の計算則を使う。
規約：Segal 1974 Proposition 1.5 の正則 bar の収縮の転置の可換性。
使われ方：全空間の比較と基底への射の可換四角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory MonoidalClosed
open scoped _root_.Simplicial

/--
概要：K-L9 の基点始点 path の終点は、通常の区間の指数の終点評価である。
方針：端点の点つき制限と非基点側の単位の評価を合成する。
規約：始点は零、終点は一。
使われ方：任意のパラメータ付き区間の族の終点計算。
-/
theorem basedPathEndpoint_evaluation (Y : PointedSimplicialSet.{u}) :
    (Spectra.pathEndpoint Y).right =
      PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y ≫ Spectra.KanPath.evaluation Y.right 1 := by
  rw [Spectra.pathEndpoint, Under.comp_right, pointedUnitIso_evaluation]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint Y ≫
    (PointedObject.basedHomι (𝟙_ PointedSimplicialSet.{u}) Y ≫
      (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶
        (𝟙_ PointedSimplicialSet.{u}).right)).app Y.right ≫
          (MonoidalClosed.unitIsoSelf (X := Y.right)).hom) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, Category.assoc]
  have he : (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right).app Y.right ≫
      (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶
        (𝟙_ PointedSimplicialSet.{u}).right)).app Y.right =
      (MonoidalClosed.pre (Spectra.KanPath.endpoint 1)).app Y.right := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl]
    rfl
  change PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y ≫
    (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right).app Y.right ≫
    (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶
      (𝟙_ PointedSimplicialSet.{u}).right)).app Y.right ≫
      (MonoidalClosed.unitIsoSelf (X := Y.right)).hom = _
  rw [← Category.assoc _ _ (MonoidalClosed.unitIsoSelf (X := Y.right)).hom, he]
  rfl

/--
概要：path space へ送った区間の族の終点評価は、元の区間の終点への制限である。
方針：基礎指数への包含と通常の curry の端点評価を計算する。
規約：始点の条件以外に Kan 性は要求しない。
使われ方：収縮からの全空間の比較の基底上での可換性。
-/
@[reassoc] theorem basedPathFamilyMap_endpoint {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right)
    (h₀ : SSet.ι₀ ≫ f = SSet.const (PointedSimplicialSet.basepoint Y)) :
    basedPathFamilyMap Y f h₀ ≫ (Spectra.pathEndpoint Y).right = SSet.ι₁ ≫ f := by
  rw [basedPathEndpoint_evaluation, ← Category.assoc, basedPathFamilyMap_ι,
    Spectra.KanPath.evaluation, ← Category.assoc, curry_pre_app,
    Spectra.KanPath.curry_unit_evaluation]
  have he : (λ_ X).inv ≫ Spectra.KanPath.endpoint 1 ▷ X ≫
      (β_ (Δ[1] : SSet.{u}) X).hom = SSet.ι₁ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  simpa only [Category.assoc] using congrArg (fun t => t ≫ f) he

end SerrePositivity.KST.Comparison
