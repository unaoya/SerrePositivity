module
public import SerrePositivity.KST.SConstruction.CofiberTensorFamilyExt
public import SerrePositivity.KST.SConstruction.PointedSuspensionEvaluation

/-! # 元の区間組み立ての全写像族自然性を suspension へ降ろす
概要：元の積上の作用の可換式を、同じ商の suspension 上の全写像族へ移す。
方針：二つの元の商射による検出と、全族の suspension 評価を合成する。
規約：局所化や逆射を選ばない。使われ方：反復 K の元の構造写像の全族整合性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra PointedSimplicialSet
open scoped Simplicial

/-- 元の商射で回収される区間組み立ての自然性は、suspension の全族自然性を与える。 -/
lemma cofiberSuspensionFamily_naturality {B X B' Y P : SSet.{u}}
    (g : B ⟶ X) (g' : B' ⟶ Y) (Z W : PointedSimplicialSet.{u})
    (σ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.cofiber g) ⟶ Z)
    (σ' : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.cofiber g') ⟶ W)
    (a : P ⟶ (PointedObject.basedHom (PointedObject.cofiber g)
      (PointedObject.cofiber g')).right)
    (b : P ⟶ (PointedObject.basedHom Z W).right)
    (s : X ⊗ P ⟶ Y) (h : (Δ[1] : SSet.{u}) ⊗ X ⟶ Z.right)
    (h' : (Δ[1] : SSet.{u}) ⊗ Y ⟶ W.right)
    (ha : (PointedObject.cofiberQuotient g ▷ P) ≫
      uncurry (a ≫ PointedObject.basedHomι _ _) = s ≫ PointedObject.cofiberQuotient g')
    (hσ : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberQuotient g) ≫ productToSmash circle (PointedObject.cofiber g) ≫
        σ.right = h)
    (hσ' : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberQuotient g') ≫ productToSmash circle (PointedObject.cofiber g') ≫
        σ'.right = h')
    (hab : (h ▷ P) ≫ uncurry (b ≫ PointedObject.basedHomι Z W) =
      (α_ (Δ[1] : SSet.{u}) X P).hom ≫ ((Δ[1] : SSet.{u}) ◁ s) ≫ h') :
    a ≫ (suspensionHom (PointedObject.cofiber g) (PointedObject.cofiber g')).right ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.cofiber g)) σ').right =
    b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre σ W := by
  apply cofiberTensorFamily_hom_ext (boundary.{u} 1).ι g W
  rw [← Category.assoc a
    (suspensionHom (PointedObject.cofiber g) (PointedObject.cofiber g')).right
    (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.cofiber g)) σ').right]
  erw [Category.assoc, pointedFamily_post_evaluation (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.cofiber g))
    (a ≫ (suspensionHom (PointedObject.cofiber g) (PointedObject.cofiber g')).right) σ',
    pointedFamily_pre_evaluation σ W b]
  ext n z
  have he := suspensionHom_family_app (PointedObject.cofiber g) (PointedObject.cofiber g')
    a n ((PointedObject.cofiberQuotient (boundary.{u} 1).ι).app n z.1.1)
      ((PointedObject.cofiberQuotient g).app n z.1.2) z.2
  have hs := types_congr_hom (NatTrans.congr_app ha n) (z.1.2, z.2)
  have hl := types_congr_hom (NatTrans.congr_app hσ n) z.1
  have hr := types_congr_hom (NatTrans.congr_app hσ' n)
    (z.1.1, s.app n (z.1.2, z.2))
  have hn := types_congr_hom (NatTrans.congr_app hab n) z
  exact (congrArg (fun x => σ'.right.app n x) he).trans
    ((congrArg (fun x => σ'.right.app n ((productToSmash circle
      (PointedObject.cofiber g')).app n
        ((PointedObject.cofiberQuotient (boundary.{u} 1).ι).app n z.1.1, x))) hs).trans
      (hr.trans (hn.symm.trans
        (congrArg (fun x => (uncurry (b ≫ PointedObject.basedHomι Z W)).app n (x, z.2))
          hl.symm))))

end SerrePositivity.KST.SConstruction
