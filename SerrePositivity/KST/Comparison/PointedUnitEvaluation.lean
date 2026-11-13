module

public import SerrePositivity.KST.Spectra.PointedVertexComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomTensorStrength
public import SerrePositivity.KST.Spectra.UnpointedPathEvaluation

/-!
# 点つき内部 Hom の単位での非基点評価

概要：零次球面からの点つき内部 Hom の単位同型を、非基点での通常の評価と同定する。
方針：smash の評価を直積上へ戻し、左単位子の逆の非基点成分を計算する。
規約：Segal 1974 Proposition 1.5 の path の終点評価と標準ループ写像の比較への補助。
使われ方：K-L9 の pathEndpoint とパラメータ付き区間写像の終点との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory MonoidalClosed

/--
概要：点つき閉構造の評価を smash の商の前へ戻すと、基礎指数の通常の評価になる。
方針：評価の curry が恒等であることを、具体的な smash の curry で計算する。
規約：源と標的の Kan 性は不要。
使われ方：点つき単位の非基点での評価。
-/
theorem pointedEvaluation_product (K Y : PointedSimplicialSet.{u}) :
    (PointedObject.smashQuotient K (PointedObject.basedHom K Y)).right ≫
      ((ihom.ev K).app Y).right = uncurry (PointedObject.basedHomι K Y) := by
  have hc : MonoidalClosed.curry ((ihom.ev K).app Y) = 𝟙 (PointedObject.basedHom K Y) := by
    rw [← uncurry_id_eq_ev, curry_uncurry]
    rfl
  rw [Spectra.PointedMapping.curry_eq_smashCurry] at hc
  apply curry_injective
  rw [curry_uncurry]
  calc
    _ = (PointedObject.smashCurry ((ihom.ev K).app Y)).right ≫
        PointedObject.basedHomι K Y := (PointedObject.smashCurry_ι _).symm
    _ = _ := by rw [hc]; rfl

/--
概要：点つき内部 Hom の単位同型は、零次球面の非基点を評価する通常の射である。
方針：単位同型を評価と左単位子で展開し、smash の商と非基点成分を計算する。
規約：非基点は零次球面の第一の余積成分。
使われ方：pathEndpoint の通常の終点評価との一致。
-/
theorem pointedUnitIso_evaluation (Y : PointedSimplicialSet.{u}) :
    (MonoidalClosed.unitIsoSelf (X := Y)).hom.right =
      PointedObject.basedHomι (𝟙_ PointedSimplicialSet.{u}) Y ≫
        (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶
          (𝟙_ PointedSimplicialSet.{u}).right)).app Y.right ≫
          (MonoidalClosed.unitIsoSelf (X := Y.right)).hom := by
  let H := PointedObject.basedHom (𝟙_ PointedSimplicialSet.{u}) Y
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.unit_evaluation]
  change (PointedObject.leftUnitInv H).right ≫
    ((ihom.ev (𝟙_ PointedSimplicialSet.{u})).app Y).right = _
  change ((λ_ H.right).inv ≫ (coprod.inl ▷ H.right) ≫
      (PointedObject.smashQuotient (𝟙_ PointedSimplicialSet.{u}) H).right) ≫
      ((ihom.ev (𝟙_ PointedSimplicialSet.{u})).app Y).right = _
  rw [Category.assoc, Category.assoc, pointedEvaluation_product]
  calc
    _ = (λ_ H.right).inv ≫ uncurry
        (PointedObject.basedHomι (𝟙_ PointedSimplicialSet.{u}) Y ≫
          (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶
            (𝟙_ PointedSimplicialSet.{u}).right)).app Y.right) := by
      rw [uncurry_pre_app]
    _ = _ := by
      rw [← Spectra.KanPath.curry_unit_evaluation, curry_uncurry]
      exact Category.assoc _ _ _

end SerrePositivity.KST.Comparison
