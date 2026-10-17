module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFull
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatIsoLiftComputation

/-! # 全導来外側左制限比較の指定K-flatモデルによる計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D)

/-- 指定右K-flatモデルへの前合成で、全導来比較の元の表示同型を回復する。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_precomp :
    Functor.isoWhiskerLeft (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E)
        (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD) =
      leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE ≪≫
        (leftRestrictionKFlatComposeIso A B C E D F).symm ≪≫
          (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).symm :=
  rightKFlatDerivedIsoOfPrecomp_precomp A C E hE _ _ _

/-- 右K-flatモデル上の全導来比較は、両側の表示同型と固定モデル比較の逆の合成。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_app_rightKFlat
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) =
      (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv ≫
          (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).inv.app Q := by
  unfold derivedBimoduleComposeLeftRestrictionIso
  rw [rightKFlatDerivedIsoOfPrecomp_hom_app]
  rfl

/-- 両側の表示を固定すると、元の固定K-flatモデルの比較を厳密に回復するsquare。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_model_square
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
        (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q =
      (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv := by
  rw [derivedBimoduleComposeLeftRestrictionIso_app_rightKFlat]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun k =>
    (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q ≫ k)
    (Category.comp_id (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv)

/-- モデル計算squareは前因子が任意の導来対象の場合にも成り立つ。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_model_square_app
    (Q : RightKFlatBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom.app
        ((bimoduleToDerived A C E).obj Q.obj)).app P ≫
        ((leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q).app P =
      ((leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q).app P ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv.app P := by
  exact NatTrans.congr_app
    (derivedBimoduleComposeLeftRestrictionIso_model_square A B C E D F hE hD Q) P

/-- 固定K-flatモデル上のsquareが同じなら、全導来比較の自然変換は一意。 -/
lemma derivedBimoduleComposeLeftRestriction_hom_unique
    {α : leftRestrictionDerivedComposeSource A B C E D F hE ⟶
      leftRestrictionDerivedComposeTarget A B C E D F hD}
    (h : ∀ Q : RightKFlatBimoduleCategory A C E,
      α.app ((bimoduleToDerived A C E).obj Q.obj) ≫
          (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q =
        (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q ≫
          (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv) :
    α = (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom := by
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  apply (cancel_mono
    ((leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q)).mp
  exact (h Q).trans
    (derivedBimoduleComposeLeftRestrictionIso_model_square A B C E D F hE hD Q).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
