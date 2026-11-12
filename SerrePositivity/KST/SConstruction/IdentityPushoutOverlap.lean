module
public import SerrePositivity.KST.SConstruction.IdentityPushoutShapes

/-! # 恒等 span の二つの正規化の重なり
概要：一方の枝を恒等にした標準 span の像の重なりでは、二つの標準四角形が厳密に一致する。
方針：各像への冪等な射を使い、交差した二つの復元が同じ一定図式となることを計算する。
規約：同型に弱めない。使われ方：二つの向きを同時に正規化する部分図式の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：span の片方の枝から標準の退化四角形を復元する。
方針：枝に制限した後、対応する座標射影で引き戻す。
規約：一般の入力では押し出しとは限らない。使われ方：恒等 span の部分での標準の選択。 -/
def identitySquareReconstruction (b : Bool) (C : SSet.{u}) :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  (pre (identitySpanSection b)).app C ≫ (pre (identityPushoutShape b)).app C

/-- 概要：標準 span の族の復元は指定した標準四角形を回収する。
方針：形状の切断の式と前合成の合成則。
規約：全単体での厳密等号。使われ方：標準四角形の普遍性。 -/
lemma identitySpanFamily_reconstruction (b : Bool) (C : SSet.{u}) :
    identitySpanFamily b C ≫ identitySquareReconstruction b C =
      (pre (identityPushoutShape b)).app C := by
  dsimp only [identitySpanFamily, identitySquareReconstruction]
  rw [← Category.assoc, ← NatTrans.comp_app, ← pre_map,
    identitySpanSection_shape, pre_id]
  simp

private lemma cross_shapes :
    ((identityPushoutShape false : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[1]) ≫
      identitySpanSection false) ≫
        (identitySpanShape true ≫ identitySpanSection true) =
      (identityPushoutShape true ≫ identitySpanSection true) ≫
        (identitySpanShape false ≫ identitySpanSection false) := by
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ fst (Δ[1] : SSet.{u}) Δ[1] =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    decide
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ snd (Δ[1] : SSet.{u}) Δ[1] =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hc₀ : identitySpanSection false ≫ identitySpanShape true =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ fst (Δ[1] : SSet.{u}) Δ[1]) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    exact h₀
  have hc₁ : identitySpanSection true ≫ identitySpanShape false =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change horn₂₀.ι₀₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ snd (Δ[1] : SSet.{u}) Δ[1]) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    exact h₁
  rw [Category.assoc, ← Category.assoc (identitySpanSection false), hc₀,
    Category.assoc, ← Category.assoc (identitySpanSection true), hc₁]
  rw [← Category.assoc, SSet.comp_const, ← Category.assoc, SSet.comp_const,
    SSet.const_comp, SSet.const_comp]
  congr 1

/-- 概要：二つの冪等な標準化を交差させた四角形の復元は一致する。
方針：両方とも共通始点で一定の図式となる形状計算を内部 Hom に移す。
規約：全単体での等号。使われ方：二つの像の重なりでの貼り合わせ。 -/
lemma identitySquareReconstruction_cross (C : SSet.{u}) :
    (pre (identitySpanSection true)).app C ≫ identitySpanFamily true C ≫
        identitySquareReconstruction false C =
      (pre (identitySpanSection false)).app C ≫ identitySpanFamily false C ≫
        identitySquareReconstruction true C := by
  simp only [identitySpanFamily, identitySquareReconstruction]
  simp only [← NatTrans.comp_app, ← pre_map]
  simpa only [Category.assoc] using
    congrArg (fun k => (pre k).app C) cross_shapes

private lemma fixed_of_range {A X : SSet.{u}} (i : A ⟶ X) (r : X ⟶ A)
    (hr : i ≫ r = 𝟙 _) (n : SimplexCategoryᵒᵖ) (v : X.obj n)
    (h : v ∈ (Subcomplex.range i).obj n) : (r ≫ i).app n v = v := by
  obtain ⟨a, rfl⟩ := h
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app hr n) a
  change r.app n (i.app n a) = a at he
  change i.app n (r.app n (i.app n a)) = _
  rw [he]

private lemma overlap_of_retractions {A B X Y : SSet.{u}}
    (i₀ : A ⟶ X) (r₀ : X ⟶ A) (i₁ : B ⟶ X) (r₁ : X ⟶ B) (f₀ f₁ : X ⟶ Y)
    (h₀ : i₀ ≫ r₀ = 𝟙 _) (h₁ : i₁ ≫ r₁ = 𝟙 _)
    (hc : (r₁ ≫ i₁) ≫ f₀ = (r₀ ≫ i₀) ≫ f₁)
    (n : SimplexCategoryᵒᵖ) (v : X.obj n)
    (hv₀ : v ∈ (Subcomplex.range i₀).obj n) (hv₁ : v ∈ (Subcomplex.range i₁).obj n) :
    f₀.app n v = f₁.app n v := by
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app hc n) v
  change f₀.app n ((r₁ ≫ i₁).app n v) = f₁.app n ((r₀ ≫ i₀).app n v) at he
  rwa [fixed_of_range i₁ r₁ h₁ n v hv₁, fixed_of_range i₀ r₀ h₀ n v hv₀] at he

/-- 概要：二つの恒等 span の像の共通部分では標準四角形が厳密に一致する。
方針：各像に属する元は対応する冪等な標準化で固定されることを使う。
規約：パラメーターの全次数で成立。使われ方：同時正規化する族の貼り合わせ。 -/
lemma identitySquareReconstruction_overlap (C : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (v : ((ihom (horn 2 0 : SSet.{u})).obj C).obj n)
    (h₀ : v ∈ (Subcomplex.range (identitySpanFamily false C)).obj n)
    (h₁ : v ∈ (Subcomplex.range (identitySpanFamily true C)).obj n) :
    (identitySquareReconstruction false C).app n v =
      (identitySquareReconstruction true C).app n v := by
  have hr (b : Bool) : identitySpanFamily b C ≫ (pre (identitySpanSection b)).app C = 𝟙 _ := by
    dsimp only [identitySpanFamily]
    rw [← NatTrans.comp_app, ← pre_map, identitySpanSection_shape, pre_id]
    rfl
  exact overlap_of_retractions _ _ _ _ _ _ (hr false) (hr true)
    (identitySquareReconstruction_cross C) n v h₀ h₁

end SerrePositivity.KST.SConstruction
