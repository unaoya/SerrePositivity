module
public import SerrePositivity.KST.SConstruction.StableOneDirectionPointedFunctor
public import SerrePositivity.KST.SConstruction.StableBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.OneDirectionReducedComparison
public import SerrePositivity.KST.SConstruction.PointedFamilyPost

/-!
概要：同じ S₁ 境界商比較の全自然同値族に対する自然性を証明する。
方針：元の商射の像で全実現比較を使い、商からの基点固定族の一意性で反映する。
規約：元の二胞体の全パラメータを保持する。使われ方：有限 BF 隣接段 span の左脚。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants

private lemma pointedCofiberFamily_evaluation_ext {K L P : SSet.{u}}
    (j : K ⟶ L) (Z : PointedSimplicialSet.{u})
    (a b : P ⟶ (PointedObject.basedHom (PointedObject.cofiber j) Z).right)
    (h : (PointedObject.cofiberQuotient j ▷ P) ≫
        uncurry (a ≫ PointedObject.basedHomι _ Z) =
      (PointedObject.cofiberQuotient j ▷ P) ≫
        uncurry (b ≫ PointedObject.basedHomι _ Z)) : a = b := by
  apply Spectra.cofiberFamily_hom_ext j Z
  apply uncurry_injective
  rw [← Category.assoc, uncurry_pre_app, ← Category.assoc, uncurry_pre_app]
  exact h

private lemma pointedCofiberFamily_comparison_ext {K L P : SSet.{u}}
    (j : K ⟶ L) (Y W Z : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom (PointedObject.cofiber j) Y).right)
    (b : P ⟶ (PointedObject.basedHom W Z).right)
    (f : Y ⟶ Z) (g : PointedObject.cofiber j ⟶ W)
    (h : (PointedObject.cofiberQuotient j ▷ P) ≫
        uncurry (a ≫ PointedObject.basedHomι _ Y) ≫ f.right =
      (PointedObject.cofiberQuotient j ▷ P) ≫ (g.right ▷ P) ≫
        uncurry (b ≫ PointedObject.basedHomι W Z)) :
    a ≫ pointedFamilyPost _ Y Z f = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre g Z := by
  apply pointedCofiberFamily_evaluation_ext j Z
  rw [Category.assoc, Category.assoc, pointedFamilyPost_evaluation,
    pointedFamily_pre_evaluation]
  exact h

/-- 概要：元の商射の像で、S₁ 比較と全商作用は可換する。
方針：両経路を降下前の実現作用へ戻し、全族比較の自然性を使う。
規約：入力の全単体を固定する。使われ方：基点固定族の一意性への入力。 -/
lemma stableOneDirectionReducedComparison_quotient_app (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj (stableCategoryModel C)).obj n)
    (p : (C ⟶[SSet.{u}] D).obj n) :
    (oneDirectionReducedComparison r (stableCategoryModel D)).right.app n
        ((stableOneDirectionReducedAction r C D).app n
          ((oneDirectionReductionQuotient r (stableCategoryModel C)).app n x, p)) =
      (stableBoundaryReducedAction r C D).app n
        ((oneDirectionReducedComparison r (stableCategoryModel C)).right.app n
          ((oneDirectionReductionQuotient r (stableCategoryModel C)).app n x), p) := by
  let X := stableCategoryModel C
  let Y := stableCategoryModel D
  have hs := types_congr_hom (NatTrans.congr_app
    (stableOneDirectionReducedAction_quotient r C D) n) (x, p)
  have ht := types_congr_hom (NatTrans.congr_app
    (oneDirectionReducedComparison_quotient r Y) n)
    ((stableOneDirectionAction (r + 1) C D).app n (x, p))
  have hf := types_congr_hom (NatTrans.congr_app
    (oneDirectionReducedComparison_quotient r X) n) x
  have hq := types_congr_hom (NatTrans.congr_app
    (stableBoundaryReducedAction_quotient r C D) n)
    ((oneDirectionRealizationComparison (r + 1) X).app n x, p)
  have hn := types_congr_hom (NatTrans.congr_app
    (stableOneDirectionComparison_action (r + 1) C D) n) (x, p)
  exact (congrArg (fun y => (oneDirectionReducedComparison r Y).right.app n y) hs).trans
    (ht.trans ((congrArg (fun y => (boundaryReductionQuotient r Y).app n y) hn.symm).trans
      (hq.symm.trans (congrArg (fun y => (stableBoundaryReducedAction r C D).app n (y, p))
        hf.symm))))

/-- 概要：元の S₁ 商比較は全基点固定 Hom 族に自然である。
方針：同じ商射への制限で全族を比較し、その一意性で元の等式を回収する。
規約：元の実比較を使う。使われ方：点つき厳密豊穣自然変換への包装。 -/
lemma stableOneDirectionReducedComparison_family (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    stableOneDirectionReducedFamilyMap r C D ≫ pointedFamilyPost
        (oneDirectionReducedRealization r (stableCategoryModel C))
        (oneDirectionReducedRealization r (stableCategoryModel D))
        (boundaryReducedRealization r (stableCategoryModel D))
        (oneDirectionReducedComparison r (stableCategoryModel D)) =
      stableBoundaryReducedFamilyMap r C D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
        (oneDirectionReducedComparison r (stableCategoryModel C))
        (boundaryReducedRealization r (stableCategoryModel D)) := by
  apply pointedCofiberFamily_comparison_ext
    (oneDirectionFatBoundary (r + 1) (stableCategoryModel C)).ι
  have ha := (congrArg (uncurry (C := SSet.{u}))
    (stableOneDirectionReducedFamilyMap_inclusion r C D)).trans (uncurry_curry _)
  have hb := (congrArg (uncurry (C := SSet.{u}))
    (stableBoundaryReducedFamilyMap_inclusion r C D)).trans (uncurry_curry _)
  let q := oneDirectionReductionQuotient r (stableCategoryModel C)
  let P := C ⟶[SSet.{u}] D
  have hl := congrArg
    (fun f => (q ▷ P) ≫ f ≫ (oneDirectionReducedComparison r (stableCategoryModel D)).right) ha
  have hr := congrArg
    (fun f => (q ▷ P) ≫
      ((oneDirectionReducedComparison r (stableCategoryModel C)).right ▷ P) ≫ f) hb
  refine hl.trans (Eq.trans ?_ hr.symm)
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact stableOneDirectionReducedComparison_quotient_app r C D n z.1 z.2

end SerrePositivity.KST.SConstruction
