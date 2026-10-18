module

public import SerrePositivity.KST.DerivedGeometry.CoefficientModuleRestriction

/-!
概要：係数加群層の開制限と構造層への忘却を比較する。
方針：同じ開上の切断と係数作用の比較を使う。
規約：対象の構造層は実際の開部分スキームの構造層。
使われ方：TT 3.19・8.1、Toën §3.2 の Dqc の開制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens)

/--
概要：係数開制限を忘却したものは基礎 O 加群層の開制限と自然同型。
方針：開部分スキームの構造層の同じ制限を使う。
規約：層の切断と射を保持する。
使われ方：TT 3.19・8.1、Toën §3.2 の準連接性の制限。
-/
def openRestrictionForgetIso :
    B.openRestriction U ⋙ (B.restrict U).forget ≅
      B.forget ⋙ Scheme.Modules.restrictFunctor U.ι := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso ?_
    refine PresheafOfModules.isoMk (fun V => ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext x
      change M.val.obj (.op (U.isOpenEmbedding.functor.obj V.unop)) at x
      change ((B.structureMap.hom.app (.op (U.isOpenEmbedding.functor.obj V.unop)))
          ((U.ι.appIso V.unop).inv r)) • x =
        ((B.structureMap.hom.app (.op (U.isOpenEmbedding.functor.obj V.unop))) r) • x
      rw [Scheme.Opens.ι_appIso]
      rfl
    · intros
      rfl
  · intro M N f
    ext V x
    rfl

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
