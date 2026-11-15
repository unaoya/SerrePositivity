module
public import SerrePositivity.HomologicalAlgebra.CopowerUnitHom
public import Mathlib.CategoryTheory.Types.Basic

/-!
概要：単位加群の係数重みからの自然変換を、元の集合値図式からの自然変換として読む。
方針：各対象の指定生成元評価を、前合成・後合成自然性で図式全体へ持ち上げる。
規約：小さい添字集合を ULift して係数加群の宇宙へ送る。全射の自然性を省略しない。
使われ方：HA 1.2.4、G10 の線形 BK 重みと集合的重みの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {D : Type v} [Category.{w} D]
variable (W : D ⥤ Type) (M : D ⥤ ModuleCat.{u} A)

/-- 指定係数余積の生成元評価を、図式の全射に自然な写像へ移す。 -/
def copowerUnitDiagramHomTo (f : W ⋙ copowerFunctor (ModuleCat.of A A) ⟶ M) :
    W ⋙ uliftFunctor.{u,0} ⟶ M ⋙ forget (ModuleCat.{u} A) where
  app d := ↾fun s => copowerUnitHomEquiv A (W.obj d) (M.obj d) (f.app d) s.down
  naturality d e h := by
    apply ConcreteCategory.hom_ext
    intro s
    have hf := congrArg (copowerUnitHomEquiv A (W.obj d) (M.obj e)) (f.naturality h)
    change copowerUnitHomEquiv A (W.obj d) (M.obj e)
      ((copowerFunctor (ModuleCat.of A A)).map (W.map h) ≫ f.app e) =
      copowerUnitHomEquiv A (W.obj d) (M.obj e) (f.app d ≫ M.map h) at hf
    rw [copowerUnitHomEquiv_precomp, copowerUnitHomEquiv_postcomp] at hf
    exact congrFun hf s.down

/-- 集合値図式の写像を、同じ指定係数余積からの自然変換へ戻す。 -/
def copowerUnitDiagramHomFrom (f : W ⋙ uliftFunctor.{u,0} ⟶ M ⋙ forget (ModuleCat.{u} A)) :
    W ⋙ copowerFunctor (ModuleCat.of A A) ⟶ M where
  app d := (copowerUnitHomEquiv A (W.obj d) (M.obj d)).symm (fun s => f.app d ⟨s⟩)
  naturality d e h := by
    apply (copowerUnitHomEquiv A (W.obj d) (M.obj e)).injective
    change copowerUnitHomEquiv A (W.obj d) (M.obj e)
      ((copowerFunctor (ModuleCat.of A A)).map (W.map h) ≫ _) =
      copowerUnitHomEquiv A (W.obj d) (M.obj e) (_ ≫ M.map h)
    rw [copowerUnitHomEquiv_precomp, copowerUnitHomEquiv_postcomp]
    simp only [Equiv.apply_symm_apply]
    funext s
    exact congrArg (fun g => g (ULift.up s)) (f.naturality h)

/-- 指定生成元の像による、図式全体の Hom 同値。 -/
def copowerUnitDiagramHomEquiv :
    (W ⋙ copowerFunctor (ModuleCat.of A A) ⟶ M) ≃
      (W ⋙ uliftFunctor.{u,0} ⟶ M ⋙ forget (ModuleCat.{u} A)) where
  toFun := copowerUnitDiagramHomTo A W M
  invFun := copowerUnitDiagramHomFrom A W M
  left_inv f := by
    apply NatTrans.ext
    funext d
    exact (copowerUnitHomEquiv A (W.obj d) (M.obj d)).symm_apply_apply (f.app d)
  right_inv f := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    exact congrFun ((copowerUnitHomEquiv A (W.obj d) (M.obj d)).apply_symm_apply
      (fun t => f.app d (ULift.up t))) s.down

/-- 図式 Hom 同値は、係数図式の全自然変換による後合成を保つ。 -/
theorem copowerUnitDiagramHomEquiv_postcomp {M N : D ⥤ ModuleCat.{u} A}
    (f : W ⋙ copowerFunctor (ModuleCat.of A A) ⟶ M) (g : M ⟶ N) :
    copowerUnitDiagramHomEquiv A W N (f ≫ g) =
      copowerUnitDiagramHomEquiv A W M f ≫ Functor.whiskerRight g (forget (ModuleCat.{u} A)) := by
  apply NatTrans.ext
  funext d
  rfl

/-- 図式 Hom 同値は、元の集合値重みの全自然変換による前合成を保つ。 -/
theorem copowerUnitDiagramHomEquiv_precomp {V W : D ⥤ Type}
    (g : V ⟶ W) (f : W ⋙ copowerFunctor (ModuleCat.of A A) ⟶ M) :
    copowerUnitDiagramHomEquiv A V M
        (Functor.whiskerRight g (copowerFunctor (ModuleCat.of A A)) ≫ f) =
      Functor.whiskerRight g uliftFunctor.{u,0} ≫ copowerUnitDiagramHomEquiv A W M f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  exact congrFun (copowerUnitHomEquiv_precomp A (M.obj d) (g.app d) (f.app d)) s.down

end SerrePositivity.HomologicalAlgebra
