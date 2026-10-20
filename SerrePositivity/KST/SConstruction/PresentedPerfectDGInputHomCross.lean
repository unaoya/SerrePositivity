module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHom

/-! # 入力 Hom の任意パラメータとの交差
概要：入力自然変換の作用と任意のラベル Hom パラメータを交換する。
方針：元の全 Hom 自然性をパラメータで前合成し、signed braiding の自然性を使う。
規約：全次数と元の交差符号を保つ。使われ方：二回の tensor dg 作用の全 Hom 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の入力 Hom と任意パラメータのラベル射は、同じ signed braiding で交換する。 -/
lemma presentedPerfectDGInputHom_cross (F G : DGFunctor A D E)
    {K : Complex A} {X Y : PresentedPerfectDGObject A D}
    (b : K ⟶ homObject A (PresentedPerfectDGObject A D) X Y) :
    (presentedPerfectDGInputHom A D E F G X ⊗ₘ
      (b ≫ (presentedPerfectDGAction A D E G).map X Y)) ≫
        eComp (Complex A) ((presentedPerfectDGAction A D E F).obj X)
          ((presentedPerfectDGAction A D E G).obj X) ((presentedPerfectDGAction A D E G).obj Y) =
      (β_ (dgFunctorHom A D E F G) K).hom ≫
        ((b ≫ (presentedPerfectDGAction A D E F).map X Y) ⊗ₘ
          presentedPerfectDGInputHom A D E F G Y) ≫
            eComp (Complex A) ((presentedPerfectDGAction A D E F).obj X)
              ((presentedPerfectDGAction A D E F).obj Y)
              ((presentedPerfectDGAction A D E G).obj Y) := by
  have h := congrArg (fun k => (𝟙 (dgFunctorHom A D E F G) ⊗ₘ b) ≫ k)
    (presentedPerfectDGInputHom_naturality A D E F G X Y)
  rw [BraidedCategory.braiding_naturality_assoc] at h
  simpa only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h.symm

end SerrePositivity.KST.SConstruction
