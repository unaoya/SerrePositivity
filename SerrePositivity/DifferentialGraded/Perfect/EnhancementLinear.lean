module
public import SerrePositivity.DifferentialGraded.Perfect.Enhancement
public import SerrePositivity.DifferentialGraded.Derived.HomotopyLinear

/-! # 射影的perfect加群によるH⁰比較の線形性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主導来比較は加法的。H⁰包含と局所化比較の合成として継承する。 -/
instance perfectDGModuleToDerivedAdditive (S : Set D) :
    (perfectDGModuleToDerived A D S).Additive := by
  dsimp [perfectDGModuleToDerived]
  infer_instance

/-- 主導来比較はA線形。既存Hom endの線形性とK(D)比較を使用する。 -/
instance perfectDGModuleToDerivedLinear (S : Set D) :
    (perfectDGModuleToDerived A D S).Linear A := by
  dsimp [perfectDGModuleToDerived]
  infer_instance

/-- Perfへの持ち上げは主導来比較の加法性を保つ。 -/
instance perfectDGModuleToPerfectAdditive (S : Set D) :
    (perfectDGModuleToPerfect A D S).Additive := by
  dsimp [perfectDGModuleToPerfect]
  infer_instance

/-- Perfへの持ち上げはA線形。充満部分圏の射の外延性で確認する。 -/
instance perfectDGModuleToPerfectLinear (S : Set D) :
    (perfectDGModuleToPerfect A D S).Linear A where
  map_smul f a := (modulePerfectOver A D S).hom_ext
    ((perfectDGModuleToDerived A D S).map_smul a f)

/-- 選択した同値の順関手は加法的比較そのものである。 -/
instance perfectDGModuleHomotopyEquivalenceFunctorAdditive (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).functor.Additive := by
  change (perfectDGModuleToPerfect A D S).Additive
  infer_instance

/-- 選択した同値の順関手はA線形。逆関手の線形性もMathlibの同値APIから得る。 -/
instance perfectDGModuleHomotopyEquivalenceFunctorLinear (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).functor.Linear A := by
  change (perfectDGModuleToPerfect A D S).Linear A
  infer_instance

/-- Perfへの比較と主導来包含の合成を、元の主導来比較と同定する自然同型。 -/
def perfectDGModuleToPerfectCompInclusion (S : Set D) :
    perfectDGModuleToPerfect A D S ⋙ perfectModuleInclusion A D S ≅
      perfectDGModuleToDerived A D S :=
  (modulePerfectOver A D S).liftCompιIso _ _

end SerrePositivity.DifferentialGraded
