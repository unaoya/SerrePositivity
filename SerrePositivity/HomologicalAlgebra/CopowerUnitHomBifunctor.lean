module
public import SerrePositivity.HomologicalAlgebra.CopowerUnitHomDiagram

/-!
概要：係数余積の Hom 同値を、単体方向と添字圏方向の両方に自然な形へ持ち上げる。
方針：各外側の対象に図式 Hom 同値を適用し、その両自然性で外側の自然変換を作る。
規約：外側・内側の全射を保持する。単体方向の各次数だけの同値ではない。
使われ方：HA 1.2.4、G10 の実正規化 BK 重みから集合的な単体写像への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v' w'
open CategoryTheory
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A]
variable {D : Type v} [Category.{w} D] {E : Type v'} [Category.{w'} E]
variable (W : D ⥤ E ⥤ Type) (M : D ⥤ E ⥤ ModuleCat.{u} A)

/-- 内側の係数余積を全二変数の集合値自然変換へ移す。 -/
def copowerUnitBifunctorHomTo
    (f : W ⋙ (Functor.whiskeringRight E (Type 0) (ModuleCat.{u} A)).obj
      (copowerFunctor (ModuleCat.of A A)) ⟶ M) :
    W ⋙ (Functor.whiskeringRight E (Type 0) (Type u)).obj uliftFunctor.{u,0} ⟶
      M ⋙ (Functor.whiskeringRight E (ModuleCat.{u} A) (Type u)).obj (forget (ModuleCat.{u} A)) where
  app d := copowerUnitDiagramHomEquiv A (W.obj d) (M.obj d) (f.app d)
  naturality d e h := by
    have hf := congrArg (copowerUnitDiagramHomEquiv A (W.obj d) (M.obj e)) (f.naturality h)
    change copowerUnitDiagramHomEquiv A (W.obj d) (M.obj e)
      (Functor.whiskerRight (W.map h) (copowerFunctor (ModuleCat.of A A)) ≫ f.app e) =
      copowerUnitDiagramHomEquiv A (W.obj d) (M.obj e) (f.app d ≫ M.map h) at hf
    rw [copowerUnitDiagramHomEquiv_precomp, copowerUnitDiagramHomEquiv_postcomp] at hf
    exact hf

/-- 全二変数の集合値自然変換から、同じ係数余積の射へ戻す。 -/
def copowerUnitBifunctorHomFrom
    (f : W ⋙ (Functor.whiskeringRight E (Type 0) (Type u)).obj uliftFunctor.{u,0} ⟶
      M ⋙ (Functor.whiskeringRight E (ModuleCat.{u} A) (Type u)).obj (forget (ModuleCat.{u} A))) :
    W ⋙ (Functor.whiskeringRight E (Type 0) (ModuleCat.{u} A)).obj
      (copowerFunctor (ModuleCat.of A A)) ⟶ M where
  app d := (copowerUnitDiagramHomEquiv A (W.obj d) (M.obj d)).symm (f.app d)
  naturality d e h := by
    apply (copowerUnitDiagramHomEquiv A (W.obj d) (M.obj e)).injective
    change copowerUnitDiagramHomEquiv A (W.obj d) (M.obj e)
      (Functor.whiskerRight (W.map h) (copowerFunctor (ModuleCat.of A A)) ≫ _) =
      copowerUnitDiagramHomEquiv A (W.obj d) (M.obj e) (_ ≫ M.map h)
    rw [copowerUnitDiagramHomEquiv_precomp, copowerUnitDiagramHomEquiv_postcomp]
    simp only [Equiv.apply_symm_apply]
    exact f.naturality h

/-- 係数余積からの射の、二変数の全自然変換としての同値。 -/
def copowerUnitBifunctorHomEquiv :
    (W ⋙ (Functor.whiskeringRight E (Type 0) (ModuleCat.{u} A)).obj
      (copowerFunctor (ModuleCat.of A A)) ⟶ M) ≃
    (W ⋙ (Functor.whiskeringRight E (Type 0) (Type u)).obj uliftFunctor.{u,0} ⟶
      M ⋙ (Functor.whiskeringRight E (ModuleCat.{u} A) (Type u)).obj (forget (ModuleCat.{u} A))) where
  toFun := copowerUnitBifunctorHomTo A W M
  invFun := copowerUnitBifunctorHomFrom A W M
  left_inv f := by
    apply NatTrans.ext
    funext d
    exact (copowerUnitDiagramHomEquiv A (W.obj d) (M.obj d)).symm_apply_apply (f.app d)
  right_inv f := by
    apply NatTrans.ext
    funext d
    exact (copowerUnitDiagramHomEquiv A (W.obj d) (M.obj d)).apply_symm_apply (f.app d)

end SerrePositivity.HomologicalAlgebra
