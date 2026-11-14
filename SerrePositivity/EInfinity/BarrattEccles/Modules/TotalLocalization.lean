module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRawFamily
public import SerrePositivity.EInfinity.BarrattEccles.AlgebraRelativeCategory
public import SerrePositivity.EInfinity.BarrattEccles.CAlg
public import SerrePositivity.EInfinity.SimplicialLocalization.NerveMap

/-!
# BE 全加群圏の同じ台と相対局所化の射影

概要：HA §4.2.3 の元の全加群圏を準同型で局所化し、同じ CAlg への実射影を作る。
方針：底と台の二つの準同型条件を取り、既存の相対局所化の nerve を使う。
規約：cocartesian 性と半自由 fiber 比較はこの射影とは別に検証する。
使われ方：BE の native な全加群族の全圏と底への射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
attribute [local implicit_reducible] strictRawModuleRestrictionPseudofunctor
variable (A : Type u) [CommRing A]

/-- 概要：元の全加群圏から同じ台の複体への忘却（HA §4.2.3）。
方針：唯一点の評価と、同じ合成比較の恒等成分を使う。
規約：底が変わる射も同じ鎖写像へ送る。使われ方：全圏の準同型条件。 -/
def strictRawModuleTotalForget : strictRawModuleTotal A ⥤ Complex A where
  obj M := (strictRawModuleUnderlying M.base).obj M.fiber
  map {M T} f := (strictRawModuleUnderlying M.base).map f.fiber
  map_id M := by
    change (strictRawModuleUnderlying M.base).map
      ((strictRawModuleRestrict_idIso M.base).inv.app M.fiber) = 𝟙 _
    exact strictRawModuleRestrict_idIso_inv_eval M.base M.fiber
  map_comp {M T P} f g := by
    change (strictRawModuleUnderlying M.base).map
      (f.fiber ≫ (strictRawModuleRestrict f.base).map g.fiber ≫
        (strictRawModuleRestrict_compIso f.base g.base).hom.app P.fiber) =
      (strictRawModuleUnderlying M.base).map f.fiber ≫ (strictRawModuleUnderlying T.base).map g.fiber
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      strictRawModuleRestrict_compIso_eval, strictRawModuleRestrict_eval]
    let a : (strictRawModuleUnderlying M.base).obj M.fiber ⟶
        (strictRawModuleUnderlying T.base).obj T.fiber :=
      (strictRawModuleUnderlying M.base).map f.fiber
    let b : (strictRawModuleUnderlying T.base).obj T.fiber ⟶
        (strictRawModuleUnderlying P.base).obj P.fiber :=
      (strictRawModuleUnderlying T.base).map g.fiber
    change a ≫ (b ≫ 𝟙 ((strictRawModuleUnderlying P.base).obj P.fiber)) = a ≫ b
    exact congrArg (fun k => a ≫ k) (Category.comp_id b)

/-- 概要：同じ底・台の準同型を反転する全加群の相対圏（HA §4.2.3）。
方針：二つの忘却による準同型類の逆像の交わりを取る。
規約：対象は元の全加群、Hom だけを宇宙上げする。使われ方：native な全圏。 -/
def strictRawModuleTotalRelative : RelativeCategory.{u+1} where
  category := Cat.of (ULiftHom.{u+1} (strictRawModuleTotal A))
  weakEquivalences :=
    ((algebraRelativeCategory A).weakEquivalences.inverseImage
      (ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleTotal A) ⋙ strictRawModuleProjection A ⋙
        ULiftHom.up.{u,u+1,u+1} (C := (operad A).Algebra))) ⊓
    ((HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
      (ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleTotal A) ⋙ strictRawModuleTotalForget A))
  isMultiplicative := inferInstance

/-- 概要：同じ全圏の射影は BE 相対圏への相対関手（HA §4.2.3）。
方針：底の準同型条件を取り出す。
規約：元の底の射を保持。使われ方：全圏の局所化から CAlg への射影。 -/
def strictRawModuleTotalProjectionRelative :
    strictRawModuleTotalRelative A ⟶ algebraRelativeCategory A where
  functor := ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleTotal A) ⋙
    strictRawModuleProjection A ⋙ ULiftHom.up.{u,u+1,u+1} (C := (operad A).Algebra)
  map := fun _ _ _ hf => hf.1

/-- 概要：同じ元の全加群相対圏の局所化準圏（HA §4.2.3）。
方針：構成済みの Kan 局所化の coherent nerve を取る。
規約：fiber の同定は別に検証する。使われ方：全加群族の全空間。 -/
abbrev moduleTotalInfinity : SSet.{u+1} := localizationNerve (strictRawModuleTotalRelative A)

/-- 概要：同じ全加群の局所化は準圏（HTT 1.1.5.10）。
方針：同じ相対圏の Kan 局所化 nerve の準圏性を使う。
規約：新しいモデル圏の仮定なし。使われ方：全加群族の全空間。 -/
instance moduleTotalInfinity_quasicategory : Quasicategory (moduleTotalInfinity A) :=
  localizationNerve_quasicategory _

/-- 概要：同じ局所化全加群準圏から CAlg への実射影（HA §4.2.3）。
方針：元の射影と同じ cofibrant 置換を相対局所化の実関手へ送る。
規約：全単体を持つ射。cocartesian 性は別に証明する。使われ方：全加群族の底。 -/
def moduleTotalProjection : moduleTotalInfinity A ⟶ CAlg_R A :=
  localizationNerveMap ((strictRawModuleTotalProjectionRelative A) ≫ algebraToCofibrantDKRelative A)

end SerrePositivity.EInfinity.BarrattEccles
