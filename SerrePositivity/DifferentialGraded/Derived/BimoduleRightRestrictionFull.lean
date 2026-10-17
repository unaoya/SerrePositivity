module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFamily
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatIsoLiftComputation

/-! # 外側の右dg作用制限と両変数の全導来合成の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)
  (hE : localHomKFlat A E)

/-- 前因子の外側右作用を既存の導来制限で制限してから合成する関手族。 -/
def rightRestrictionDerivedComposeSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D E) :=
  derivedBimoduleComposeFunctor A D C E hE ⋙
    (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 合成後の外側右作用を既存の導来制限で制限する関手族。 -/
def rightRestrictionDerivedComposeTarget : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D E) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D E B E F (DGFunctor.id E))

def rightRestrictionDerivedComposeSourceBaseIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        rightRestrictionDerivedComposeSource A B D C E F hE ≅
      rightRestrictionKFlatComposeSource A B D C E F :=
  Functor.isoWhiskerRight (rightKFlatComposePresentationIso A C E hE D)
    ((whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C)))

def rightRestrictionDerivedComposeTargetBaseIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        rightRestrictionDerivedComposeTarget A B D C E F hE ≅
      rightRestrictionKFlatComposeTarget A B D C E F :=
  Functor.isoWhiskerRight (rightKFlatComposePresentationIso A C E hE B)
    ((whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)))

/-- 外側右作用の制限は、両変数の全導来合成と自然に可換する。 -/
def derivedBimoduleComposeRightRestrictionIso :
    rightRestrictionDerivedComposeSource A B D C E F hE ≅
      rightRestrictionDerivedComposeTarget A B D C E F hE :=
  rightKFlatDerivedIsoOfPrecomp A C E hE _ _
    (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE ≪≫
      rightRestrictionKFlatComposeIso A B D C E F ≪≫
        (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).symm)

/-- 任意の指定右K-flat後因子上で、移送前の固定モデル比較を回復する。 -/
lemma derivedBimoduleComposeRightRestrictionIso_app_rightKFlat
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) =
      (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q).hom ≫
          (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).inv.app Q := by
  unfold derivedBimoduleComposeRightRestrictionIso
  rw [rightKFlatDerivedIsoOfPrecomp_hom_app]
  rfl

lemma derivedBimoduleComposeRightRestrictionIso_model_square
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
        (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q =
      (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q).hom := by
  rw [derivedBimoduleComposeRightRestrictionIso_app_rightKFlat]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun k =>
    (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q ≫ k)
    (Category.comp_id (derivedComposeWithRightRestrictionIso A B D C E F Q).hom)

/-- 指定モデル上の同じsquareを満たす全導来比較の自然変換は一意。 -/
lemma derivedBimoduleComposeRightRestriction_hom_unique
    {α : rightRestrictionDerivedComposeSource A B D C E F hE ⟶
      rightRestrictionDerivedComposeTarget A B D C E F hE}
    (h : ∀ Q : RightKFlatBimoduleCategory A C E,
      α.app ((bimoduleToDerived A C E).obj Q.obj) ≫
          (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q =
        (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q ≫
          (derivedComposeWithRightRestrictionIso A B D C E F Q).hom) :
    α = (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom := by
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  apply (cancel_mono
    ((rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q)).mp
  exact (h Q).trans
    (derivedBimoduleComposeRightRestrictionIso_model_square A B D C E F hE Q).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
