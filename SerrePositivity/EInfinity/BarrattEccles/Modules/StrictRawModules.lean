module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 厳密 BE 底上の同じ dg 加群の相対圏

概要：HA §4.2.3 の加群族の局所化前の fiber と restriction を構成する。
方針：元の閉零加群圏と objectwise 準同型を保持し、同じ制限の法則を使う。
規約：native な全族の降下をこの通常の相対圏だけで代用しない。
使われ方：BE 加群の全族に対する相対 Grothendieck 構成の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (A : Type u) [CommRing A]

/-- 概要：厳密 BE 底上の元の閉零加群圏（HA §4.2.1）。
方針：同じ carrier の一対象 dg 圏の加群を取る。
規約：半自由性を要求しない。使われ方：局所化前の fiber。 -/
abbrev strictRawModuleCategory (X : (operad A).Algebra) :=
  ModuleCategory A (dgAlgebraCategory A ((assocForget A).obj X))

/-- 概要：同じ加群と準同型を持つ相対圏（HA §4.2.3）。
方針：objectwise 準同型の既存の乗法性を使う。
規約：元の加群を対象に持つ。使われ方：全族の相対局所化。 -/
def strictRawModuleRelativeCategory (X : (operad A).Algebra) : RelativeCategory.{u+1} where
  category := Cat.of (ULiftHom.{u+1} (strictRawModuleCategory A X))
  weakEquivalences := (moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))).inverseImage
    (ULiftHom.down.{u, u+1, u+1} (C := strictRawModuleCategory A X))
  isMultiplicative := inferInstance

variable {A}
/-- 概要：厳密 BE 射に沿う元の閉零制限（HA §4.2.3）。
方針：同じ dg 代数射に沿う前合成を使う。
規約：出力の解像度をまだ取らない。使われ方：相対圏の反変な辺。 -/
def strictRawModuleRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleCategory A Y ⥤ strictRawModuleCategory A X :=
  moduleRestriction A _ _ (dgAlgebraMap A ((assocForget A).map f)).op

/-- 概要：元の制限は objectwise 準同型を保つ（HA §4.2.3）。
方針：同じ dg 制限の準同型保存を適用。
規約：半自由性保存は不要。使われ方：全族の局所化への入力。 -/
def strictRawModuleRestrictRelative {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRelativeCategory A Y ⟶ strictRawModuleRelativeCategory A X where
  functor := ULiftHom.down.{u, u+1, u+1} (C := strictRawModuleCategory A Y) ⋙
    strictRawModuleRestrict f ⋙ ULiftHom.up.{u, u+1, u+1} (C := strictRawModuleCategory A X)
  map := fun _ _ g hg => moduleRestriction_quasiIso A _ _ _ g.down hg

/-- 概要：元の閉零制限の恒等比較（HA §4.2.3）。
方針：同じ一対象 dg 関手の恒等則を使う。
規約：既存の moduleRestrictionIdIso。使われ方：相対族の単位。 -/
def strictRawModuleRestrict_idIso (X : (operad A).Algebra) :
    strictRawModuleRestrict (𝟙 X) ≅ 𝟭 (strictRawModuleCategory A X) := by
  unfold strictRawModuleRestrict
  rw [CategoryTheory.Functor.map_id, algebraMap_id, DGFunctor.op_id]
  exact moduleRestrictionIdIso A _

/-- 概要：元の閉零制限の反変な合成比較（HA §4.2.3）。
方針：同じ一対象 dg 関手の合成則を使う。
規約：既存の graphRestrictionCompositionIso。使われ方：相対族の合成。 -/
def strictRawModuleRestrict_compIso {X Y Z : (operad A).Algebra} (f : X ⟶ Y) (g : Y ⟶ Z) :
    strictRawModuleRestrict g ⋙ strictRawModuleRestrict f ≅ strictRawModuleRestrict (f ≫ g) := by
  unfold strictRawModuleRestrict
  rw [CategoryTheory.Functor.map_comp, algebraMap_comp]
  exact graphRestrictionCompositionIso A _ _ _ _ _

/-- 概要：同じ台を取る通常の評価関手（HA §4.2.1）。
方針：一対象 dg 圏の唯一点で評価する。
規約：元の複体。使われ方：相対族の coherence の検証。 -/
def strictRawModuleUnderlying (X : (operad A).Algebra) : strictRawModuleCategory A X ⥤ Complex A :=
  moduleEvaluation A _ (Opposite.op DGAlgebraPoint.star)

/-- 概要：唯一点の評価は加群射を検出する（HA §4.2.1）。
方針：全評価による元の加群射の外延性を、一対象で使う。
規約：元の閉零射。使われ方：相対族の比較の coherence。 -/
lemma strictRawModuleHom_ext {X : (operad A).Algebra} {M T : strictRawModuleCategory A X}
    {f g : M ⟶ T} (h : (strictRawModuleUnderlying X).map f = (strictRawModuleUnderlying X).map g) :
    f = g := by
  apply moduleMorphism_ext
  intro x
  have hx : x = Opposite.op DGAlgebraPoint.star := Subsingleton.elim _ _
  subst x
  exact h

/-- 概要：恒等制限の比較は同じ台で恒等（HA §4.2.3）。
方針：既存の加群単位比較の評価式を使う。
規約：指定の同じ比較。使われ方：相対族の単位 coherence。 -/
lemma strictRawModuleRestrict_idIso_eval (X : (operad A).Algebra) (M : strictRawModuleCategory A X) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_idIso X).hom.app M) =
      𝟙 ((strictRawModuleUnderlying X).obj M) := by
  dsimp [strictRawModuleRestrict_idIso]
  simp only [moduleRestrictionIdIso, NatIso.ofComponents_hom_app,
    strictRawModuleUnderlying, moduleRestrictionIdObjIso_hom_eval]
  rfl

/-- 概要：合成制限の比較は同じ台で恒等（HA §4.2.3）。
方針：既存の加群合成比較の評価式を使う。
規約：指定の同じ比較。使われ方：相対族の結合 coherence。 -/
lemma strictRawModuleRestrict_compIso_eval {X Y Z : (operad A).Algebra}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : strictRawModuleCategory A Z) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_compIso f g).hom.app M) =
      𝟙 ((strictRawModuleUnderlying Z).obj M) := by
  dsimp [strictRawModuleRestrict_compIso]
  simp only [graphRestrictionCompositionIso, NatIso.ofComponents_hom_app,
    strictRawModuleUnderlying, moduleIsoMk_hom_eval, Iso.refl_hom]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
