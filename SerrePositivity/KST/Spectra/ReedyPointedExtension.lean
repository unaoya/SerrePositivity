module

public import SerrePositivity.KST.Spectra.CosimplicialHornFibration
public import SerrePositivity.KST.Spectra.PointedCosimplicialKanReplacement

/-!
概要：Reedy anodyne な点つき図式の射に沿って、Reedy Kan な係数への点つき自然変換を延長する。
方針：基礎図式の Reedy 充填を使い、元の基点は左射の像に含まれることから基点保存を得る。
規約：延長は実際の自然変換で、元の射との合成が厳密に等しい。
使われ方：Goerss–Jardine VII §4、BF 1978 §2。Reedy 置換後の Ω 随伴構造の構成。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.ReedyPointedExtension
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reedy anodyne な点つき図式の射に沿う厳密な点つき延長が存在する。 -/
theorem exists_extension {X Y Z : CosimplicialObject PointedSimplicialSet.{u}}
    (i : X ⟶ Y)
    (hi : reedyLeft simplex anodyneExtensions (Functor.whiskerRight i PointedSimplicialSet.forget))
    (hZ : reedyRight simplex J.rlp (terminal.from (Z ⋙ PointedSimplicialSet.forget)))
    (a : X ⟶ Z) : ∃ b : Y ⟶ Z, i ≫ b = a := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  let i' := Functor.whiskerRight i PointedSimplicialSet.forget
  let a' := Functor.whiskerRight a PointedSimplicialSet.forget
  let : ∀ j, HasLiftingProperty (relativeLatchingMap simplex j i')
      (relativeMatchingMap simplex j (terminal.from (Z ⋙ PointedSimplicialSet.forget))) :=
    fun j ↦ MorphismProperty.hasLiftingProperty_of_wfs _ _ (hi j) (hZ j)
  let : HasLiftingProperty i' (terminal.from (Z ⋙ PointedSimplicialSet.forget)) :=
    Lifting.hasLiftingProperty simplex
  let q : CommSq a' i' (terminal.from (Z ⋙ PointedSimplicialSet.forget)) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  let b : Y ⟶ Z := {
    app j := Under.homMk (q.lift.app j) (by
      have he := NatTrans.congr_app q.fac_left j
      change (i.app j).right ≫ q.lift.app j = (a.app j).right at he
      rw [← Under.w (i.app j), Category.assoc, he, Under.w (a.app j)])
    naturality j k f := by
      apply Under.UnderMorphism.ext
      exact q.lift.naturality f }
  refine ⟨b, ?_⟩
  apply NatTrans.ext
  funext j
  apply Under.UnderMorphism.ext
  exact NatTrans.congr_app q.fac_left j

end
end SerrePositivity.KST.Spectra.ReedyPointedExtension
