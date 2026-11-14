module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRawFiber

/-!
# 元の BE 加群全圏の指定 Cartesian lift の相対性

概要：HA §4.2.3 の制限の標準 Cartesian lift が、同じ台で恒等となることを示す。
方針：既存の Grothendieck lift を使い、底と台の準同型条件を照合する。
規約：通常の Cartesian 性。native な cocartesian 性は別に証明する。
使われ方：底の弱同値に沿う lift の局所化での反転。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory CategoryTheory.Functor SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
attribute [local implicit_reducible] strictRawModuleRestrictionPseudofunctor
variable (A : Type u) [CommRing A]

/-- 概要：元の全加群の射影は通常の fibered category（HA §4.2.3）。
方針：既存の反変 Grothendieck 構成の fibered 性を使う。
規約：局所化前の同じ射影。使われ方：同じ Cartesian lift の普遍性。 -/
instance strictRawModuleProjection_isFibered : IsFibered (strictRawModuleProjection A) := by
  change IsFibered (Pseudofunctor.CoGrothendieck.forget (strictRawModuleRestrictionPseudofunctor A))
  infer_instance

/-- 概要：元の制限に沿う同じ標準 Cartesian lift（HA §4.2.3）。
方針：底の射と、制限加群の恒等射を取る。
規約：元の制限加群。使われ方：局所化後の transport の指定。 -/
def strictRawModuleCartesianLift {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    (strictRawModuleFiberInclusion A X).obj ((strictRawModuleRestrict f).obj M) ⟶
      (strictRawModuleFiberInclusion A Y).obj M :=
  Pseudofunctor.CoGrothendieck.cartesianLift (F := strictRawModuleRestrictionPseudofunctor A) M f

/-- 概要：同じ標準 lift は通常の強い Cartesian 性を持つ（HA §4.2.3）。
方針：既存の同じ Grothendieck lift の普遍性を使う。
規約：元の二成分を保つ。使われ方：相対局所化の transport の比較。 -/
lemma strictRawModuleCartesianLift_isStronglyCartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    IsStronglyCartesian (strictRawModuleProjection A) f (strictRawModuleCartesianLift A f M) :=
  Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := strictRawModuleRestrictionPseudofunctor A) M f

/-- 概要：標準 lift の同じ台は恒等射（HA §4.2.3）。
方針：制限加群の恒等射を評価する。
規約：同じ台の複体。使われ方：全圏の準同型条件の後半。 -/
lemma strictRawModuleCartesianLift_underlying {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    (strictRawModuleTotalForget A).map (strictRawModuleCartesianLift A f M) =
      𝟙 ((strictRawModuleUnderlying Y).obj M) := by
  change (strictRawModuleUnderlying X).map (𝟙 ((strictRawModuleRestrict f).obj M)) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- 概要：底の弱同値に沿う標準 lift は指定準同型（HA §4.2.3）。
方針：底は元の弱同値、台は恒等射であることを使う。
規約：同じ全圏の指定弱同値。使われ方：native な底の弱同値の反転。 -/
lemma strictRawModuleCartesianLift_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    (strictRawModuleTotalRelative A).weakEquivalences
      ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)).map
        (strictRawModuleCartesianLift A f M)) := by
  constructor
  · change @HomotopicalAlgebra.weakEquivalences (operad A).Algebra _
      (modelCategory A).categoryWithWeakEquivalences _ _ f
    rw [modelCategory_weakEquivalences]
    exact hf
  · change QuasiIso ((strictRawModuleTotalForget A).map (strictRawModuleCartesianLift A f M))
    rw [strictRawModuleCartesianLift_underlying]
    exact _root_.quasiIso_of_isIso (𝟙 ((strictRawModuleUnderlying Y).obj M))

end SerrePositivity.EInfinity.BarrattEccles
