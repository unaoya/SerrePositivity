module
public import SerrePositivity.KST.SConstruction.PointedClosedEvaluation
public import SerrePositivity.KST.Spectra.CofiberMappingFamilies

/-! # 同じ商射を保つ点つき比較の全族自然性
概要：元の商射に沿う作用の可換性を、同じ点つき商からの全写像族の可換性へ移す。
方針：商の pushout の検出を、基点固定写像族の元の直積上の評価へ移す。
規約：比較の逆射や Kan 性は仮定しない。使われ方：元の S₁ 境界商比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra

/-- 商からの全基点固定写像族は、元の商射上の実作用で一意に決まる。 -/
lemma cofiberFamily_raw_hom_ext {B X P : SSet.{u}} (j : B ⟶ X)
    (Z : PointedSimplicialSet.{u})
    {a b : P ⟶ (PointedObject.basedHom (PointedObject.cofiber j) Z).right}
    (h : (PointedObject.cofiberQuotient j ▷ P) ≫
        uncurry (a ≫ PointedObject.basedHomι _ Z) =
      (PointedObject.cofiberQuotient j ▷ P) ≫
        uncurry (b ≫ PointedObject.basedHomι _ Z)) : a = b := by
  apply cofiberFamily_hom_ext j Z
  apply uncurry_injective
  erw [← Category.assoc a, ← Category.assoc b,
    uncurry_pre_app Z.right (a ≫ PointedObject.basedHomι (PointedObject.cofiber j) Z)
      (PointedObject.cofiberQuotient j),
    uncurry_pre_app Z.right (b ≫ PointedObject.basedHomι (PointedObject.cofiber j) Z)
      (PointedObject.cofiberQuotient j)]
  exact h

/-- 商射上の全単体の可換性から、同じ基点固定写像族の比較を得る。 -/
lemma cofiberFamily_comparison_of_app {B X P : SSet.{u}} (j : B ⟶ X)
    (Z V W : PointedSimplicialSet.{u}) (σ : PointedObject.cofiber j ⟶ Z)
    (τ : V ⟶ W)
    (a : P ⟶ (PointedObject.basedHom (PointedObject.cofiber j) V).right)
    (b : P ⟶ (PointedObject.basedHom Z W).right)
    (h : ∀ n (x : X.obj n) (p : P.obj n),
      τ.right.app n ((uncurry (a ≫ PointedObject.basedHomι _ V)).app n
        ((PointedObject.cofiberQuotient j).app n x, p)) =
      (uncurry (b ≫ PointedObject.basedHomι Z W)).app n
        (σ.right.app n ((PointedObject.cofiberQuotient j).app n x), p)) :
    a ≫ (PointedObject.basedHomMap (PointedObject.cofiber j) τ).right =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre σ W := by
  apply cofiberFamily_raw_hom_ext j W
  erw [Category.assoc, pointedFamily_post_evaluation (PointedObject.cofiber j) a τ,
    pointedFamily_pre_evaluation σ W b]
  ext n z
  exact h n z.1 z.2

/-- 元の商射回収を保つ比較の全作用自然性は、点つき全写像族の厳密自然性になる。 -/
lemma cofiberFamily_comparison {B X B' Y P : SSet.{u}}
    (j : B ⟶ X) (k : B' ⟶ Y) (Z W : PointedSimplicialSet.{u})
    (σ : PointedObject.cofiber j ⟶ Z) (τ : PointedObject.cofiber k ⟶ W)
    (a : P ⟶ (PointedObject.basedHom (PointedObject.cofiber j)
      (PointedObject.cofiber k)).right)
    (b : P ⟶ (PointedObject.basedHom Z W).right)
    (s : X ⊗ P ⟶ Y) (f : X ⟶ Z.right) (g : Y ⟶ W.right)
    (ha : (PointedObject.cofiberQuotient j ▷ P) ≫
      uncurry (a ≫ PointedObject.basedHomι _ _) = s ≫ PointedObject.cofiberQuotient k)
    (hσ : PointedObject.cofiberQuotient j ≫ σ.right = f)
    (hτ : PointedObject.cofiberQuotient k ≫ τ.right = g)
    (hn : (f ▷ P) ≫ uncurry (b ≫ PointedObject.basedHomι Z W) = s ≫ g) :
    a ≫ (PointedObject.basedHomMap (PointedObject.cofiber j) τ).right =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre σ W := by
  apply cofiberFamily_raw_hom_ext j W
  erw [Category.assoc, pointedFamily_post_evaluation (PointedObject.cofiber j) a τ,
    pointedFamily_pre_evaluation σ W b]
  ext n z
  have hs := types_congr_hom (NatTrans.congr_app ha n) z
  have hf := types_congr_hom (NatTrans.congr_app hσ n) z.1
  have hg := types_congr_hom (NatTrans.congr_app hτ n) (s.app n z)
  have h := types_congr_hom (NatTrans.congr_app hn n) z
  exact (congrArg (fun x => τ.right.app n x) hs).trans
    (hg.trans (h.symm.trans
      (congrArg (fun x => (uncurry (b ≫ PointedObject.basedHomι Z W)).app n (x, z.2)) hf.symm)))

end SerrePositivity.KST.SConstruction
