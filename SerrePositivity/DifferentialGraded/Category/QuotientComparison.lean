module
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Whiskering

/-! # 境界商の比較自然同型の代表上の計算

実際の大きいdg加群構成を展開せず、商・関手等式・右whiskeringを抽象的に評価する。
-/
@[expose] public section
noncomputable section
universe u v u' v' u'' v''
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
  {D : Type u''} [Category.{v''} D]

/-- 商へ降ろした、関手等式と右whiskeringを含む比較を元の代表で評価する。 -/
lemma quotientComparison_hom_app (r : HomRel C)
    (F G : Quotient r ⥤ D) (U V : C ⥤ E) (J : E ⥤ D)
    (h₁ : Quotient.functor r ⋙ F = U ⋙ J) (h₂ : U = V)
    (e : V ⋙ J ≅ Quotient.functor r ⋙ G) (X : C) :
    (Quotient.natIsoLift r
      (eqToIso h₁ ≪≫ Functor.isoWhiskerRight (eqToIso h₂) J ≪≫ e)).hom.app
        ((Quotient.functor r).obj X) =
      eqToHom (congrArg (fun H : C ⥤ D => H.obj X) h₁) ≫
        J.map (eqToHom (congrArg (fun H : C ⥤ E => H.obj X) h₂)) ≫ e.hom.app X := by
  simp [Quotient.natIsoLift, eqToHom_app]

/-- 関手等式の後の左whiskeringを対象で評価し、等式輸送を対象の等式へ落とす。 -/
lemma comparisonWhiskerLeft_hom_app (F : C ⥤ D) (I : C ⥤ E) (U V : E ⥤ D)
    (h : F = I ⋙ U) (e : U ≅ V) (X : C) :
    (eqToIso h ≪≫ Functor.isoWhiskerLeft I e).hom.app X =
      eqToHom (congrArg (fun H : C ⥤ D => H.obj X) h) ≫ e.hom.app (I.obj X) := by
  simp [eqToHom_app]

/-- 結合子で括弧を揃えて二つの比較を合成すると、成分は写像した第一成分と第二成分の合成になる。 -/
lemma comparisonCompose_hom_app (S : C ⥤ C) (I : C ⥤ E) (L : E ⥤ D)
    (K : E ⥤ E) (T : D ⥤ D) (a : S ⋙ I ≅ I ⋙ K) (b : K ⋙ L ≅ L ⋙ T) (X : C) :
    ((Functor.associator S I L).symm ≪≫ Functor.isoWhiskerRight a L ≪≫
      Functor.associator I K L ≪≫ Functor.isoWhiskerLeft I b ≪≫
      (Functor.associator I L T).symm).hom.app X =
        L.map (a.hom.app X) ≫ b.hom.app (I.obj X) := by
  simp

end SerrePositivity.DifferentialGraded
