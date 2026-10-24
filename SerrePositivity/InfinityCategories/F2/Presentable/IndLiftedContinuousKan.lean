module

public import SerrePositivity.InfinityCategories.F2.Ind.IndContinuousLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.F2.Compact.Definition
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseCoconeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftKanCanonical

/-!
概要：元の小さい filtered 余極限を保つ大きい関手の、持ち上げた Ind Yoneda に沿う左 Kan 条件。
方針：元の標準 Kan 余錐を小さい元の圏へ制限してから持ち上げ、同じ保存性を使う。
規約：大きい宇宙の添字の保存性を追加入力にしない。
使われ方：元の小さい生成圏上の Hom retract を全域へ延長する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 2}} [Quasicategory D]
  (H : (SSet.uliftFunctor.{u + 2, u + 1}).obj (IndInfinity κ C) ⟶ D)
  (hH : Compact.PreservesKappaFilteredColimits.{u, u + 1} κ H)
include hH

/-- 概要：元の標準恒等 Kan 余錐の持ち上げを、大きい関手が余極限へ写す。
方針：同じ小さい元の圏との比較同値へ制限し、元の密度余錐の保存性を適用する。
規約：元の指定頂点と全余錐を保持する。
使われ方：大きい関手の全標準左 Kan 条件。 -/
lemma indLiftedCanonical_image_isColimit (v : (IndInfinity κ C) _⦋0⦌) :
    IsColimitCone (mapJoinCocone H (JoinCocone.ulift.{u + 1, u + 2}
      (leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C)) v))) := by
  let c := leftKanCanonicalCocone (indYoneda κ C) (𝟙 (IndInfinity κ C)) v
  let e := indElementsLeftKanComparison κ v
  have := indVertexElements_isKappaFiltered κ v
  have hd := hH _ _ (indVertexDensityCocone κ v) (indVertexDensityCocone_isColimit κ v)
  have hv : (c.restrict e).val = (indVertexDensityCocone κ v).val := by
    simpa only [mapJoinCocone, Category.comp_id] using
      indLeftKanCanonicalCocone_restrict_val κ (𝟙 (IndInfinity κ C)) v
  apply (isColimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e)
    (IsQCatEquivalence.ulift.{u + 1, u + 2}
      (indElementsLeftKanComparison_isQCatEquivalence κ v)) _).mpr
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hd
  change joinMap ((SSet.uliftFunctor.{u + 2, u + 1}).map e) (𝟙 _) ≫
    ((JoinCocone.ulift.{u + 1, u + 2} c).val ≫ H) = _
  rw [← Category.assoc, ← ulift_restrictJoinCocone_val]
  change ((uliftCoconeShapeIso _ 0).inv ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (c.restrict e).val) ≫ H = _
  rw [hv]
  rfl

/-- 概要：大きい κ-連続関手は元の Yoneda の持ち上げに沿う全標準左 Kan 条件を満たす。
方針：元の恒等 Kan 余錐の像を宇宙変更の標準局所公式に渡す。
規約：要求する保存性の添字は元の宇宙 u のもののみ。
使われ方：生成対象上の全自然な分裂を元の圏の全域へ戻す。 -/
lemma indLiftedContinuous_canonicalColimits :
    ∀ v : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (IndInfinity κ C)) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C)) H v) := by
  rintro ⟨v⟩
  have h := leftKanCanonicalCocone_post_ulift_isColimit (indYoneda κ C)
    (𝟙 (IndInfinity κ C)) v H (indLiftedCanonical_image_isColimit κ H hH v)
  have heq : (SSet.uliftFunctor.{u + 2, u + 1}).map (𝟙 (IndInfinity κ C)) ≫ H = H := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [heq] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
