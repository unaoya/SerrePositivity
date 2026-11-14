module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.TotalLocalization
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import SerrePositivity.EInfinity.SimplicialLocalization.NerveFunctor

/-!
# 固定 BE 底の元の加群 fiber と全圏への包含

概要：HA §4.2.3 の元の固定底の加群を同じ Grothendieck 全圏に含める。
方針：既存の包含と通常の fiber 同値を使い、台と準同型条件を照合する。
規約：局所化後の fiber 同値・cocartesian 性は別に検証する。
使われ方：M10 の同じ半自由 fiber との native 比較への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory CategoryTheory.Functor SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
attribute [local implicit_reducible] strictRawModuleRestrictionPseudofunctor
variable (A : Type u) [CommRing A]

/-- 概要：固定底の元の加群を同じ全圏に含める（HA §4.2.3）。
方針：指定擬関手の Grothendieck 包含を使う。
規約：対象は同じ加群。使われ方：元の fiber からの比較。 -/
def strictRawModuleFiberInclusion (X : (operad A).Algebra) :
    strictRawModuleCategory A X ⥤ strictRawModuleTotal A :=
  Pseudofunctor.CoGrothendieck.ι (strictRawModuleRestrictionPseudofunctor A) X

/-- 概要：包含後の射影は同じ底の定数関手（HA §4.2.3）。
方針：同じ Grothendieck 包含の既存の射影公式を使う。
規約：関手の厳密な等式。使われ方：通常の fiber の指定比較。 -/
lemma strictRawModuleFiberInclusion_projection (X : (operad A).Algebra) :
    strictRawModuleFiberInclusion A X ⋙ strictRawModuleProjection A =
      (Functor.const (strictRawModuleCategory A X)).obj X :=
  Pseudofunctor.CoGrothendieck.comp_const (strictRawModuleRestrictionPseudofunctor A) X

/-- 概要：包含後の台は同じ元の複体（HA §4.2.3）。
方針：指定単位比較の逆成分の恒等評価を使う。
規約：対象だけでなく射も同じ。使われ方：相対包含の準同型保存。 -/
lemma strictRawModuleFiberInclusion_forget (X : (operad A).Algebra) :
    strictRawModuleFiberInclusion A X ⋙ strictRawModuleTotalForget A = strictRawModuleUnderlying X := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro M T f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (strictRawModuleUnderlying X).map (f ≫ (strictRawModuleRestrict_idIso X).inv.app T) =
    (strictRawModuleUnderlying X).map f
  rw [CategoryTheory.Functor.map_comp, strictRawModuleRestrict_idIso_inv_eval]
  exact Category.comp_id _

/-- 概要：固定底の元の加群圏は同じ通常の fiber と同値（HA §4.2.3）。
方針：同じ Grothendieck 包含から既存の fiber 同値を取る。
規約：native な局所化 fiber 同値とは区別する。使われ方：全族の固定底の入口。 -/
def strictRawModuleFiberEquivalence (X : (operad A).Algebra) :
    strictRawModuleCategory A X ≌ Functor.Fiber (strictRawModuleProjection A) X := by
  letI : (Functor.Fiber.inducedFunctor (strictRawModuleFiberInclusion_projection A X)).IsEquivalence := by
    change (Functor.Fiber.inducedFunctor
      (Pseudofunctor.CoGrothendieck.comp_const (strictRawModuleRestrictionPseudofunctor A) X)).IsEquivalence
    infer_instance
  exact (Functor.Fiber.inducedFunctor (strictRawModuleFiberInclusion_projection A X)).asEquivalence

/-- 概要：同じ固定底の包含は準同型を保つ相対関手（HA §4.2.3）。
方針：底の恒等射と、台の忘却の同じ関手等式を使う。
規約：同じ元の準同型。使われ方：全圏の局所化への包含。 -/
def strictRawModuleFiberInclusionRelative (X : (operad A).Algebra) :
    strictRawModuleRelativeCategory A X ⟶ strictRawModuleTotalRelative A where
  functor := ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X) ⋙
    strictRawModuleFiberInclusion A X ⋙ ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)
  map := by
    intro M T f hf
    constructor
    · change (algebraRelativeCategory A).weakEquivalences (𝟙 (ULiftHom.objUp.{u+1,u+1} X))
      exact (algebraRelativeCategory A).isMultiplicative.id_mem _
    · change ((HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
        (strictRawModuleFiberInclusion A X ⋙ strictRawModuleTotalForget A)) f.down
      rw [strictRawModuleFiberInclusion_forget]
      exact hf (Opposite.op DGAlgebraPoint.star)

/-- 概要：固定底の相対定数関手（HA §4.2.3）。
方針：全ての射を同じ底の恒等射へ送る。
規約：同じ BE 代数。使われ方：相対包含の底の指定。 -/
def strictRawModuleFiberBaseRelative (X : (operad A).Algebra) :
    strictRawModuleRelativeCategory A X ⟶ algebraRelativeCategory A where
  functor := (Functor.const (strictRawModuleRelativeCategory A X).category).obj (ULiftHom.objUp.{u+1,u+1} X)
  map := fun _ _ _ _ => (algebraRelativeCategory A).isMultiplicative.id_mem _

/-- 概要：相対包含の射影は同じ相対定数関手（HA §4.2.3）。
方針：元の底の成分で関手を照合する。
規約：相対関手の厳密な等式。使われ方：局所化の全単体での可換式。 -/
lemma strictRawModuleFiberInclusionRelative_projection (X : (operad A).Algebra) :
    strictRawModuleFiberInclusionRelative A X ≫ strictRawModuleTotalProjectionRelative A =
      strictRawModuleFiberBaseRelative A X := by
  apply relativeFunctor_ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro M T f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：固定底の元の加群の局所化から同じ全圏への実包含（HA §4.2.3）。
方針：同じ相対包含に既存の局所化 nerve 関手を適用する。
規約：全単体を持つ実写像。使われ方：native fiber の比較の入口。 -/
def moduleRawFiberInclusion (X : (operad A).Algebra) :
    localizationNerve (strictRawModuleRelativeCategory A X) ⟶ moduleTotalInfinity A :=
  localizationNerveMap (strictRawModuleFiberInclusionRelative A X)

/-- 概要：局所化した包含の底は同じ相対定数関手の像（HA §4.2.3）。
方針：相対局所化の合成則と元の射影の等式を使う。
規約：全単体での等式。使われ方：指定した底上の native 比較。 -/
lemma moduleRawFiberInclusion_projection (X : (operad A).Algebra) :
    moduleRawFiberInclusion A X ≫ moduleTotalProjection A =
      localizationNerveMap (strictRawModuleFiberBaseRelative A X ≫ algebraToCofibrantDKRelative A) := by
  rw [moduleRawFiberInclusion, moduleTotalProjection, ← localizationNerveMap_comp,
    ← Category.assoc, strictRawModuleFiberInclusionRelative_projection]

end SerrePositivity.EInfinity.BarrattEccles
