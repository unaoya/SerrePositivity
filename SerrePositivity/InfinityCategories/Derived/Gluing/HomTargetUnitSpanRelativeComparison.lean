module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizationInputEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputHomotopies
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientInputPathLegs
public import SerrePositivity.InfinityCategories.Derived.Gluing.InputHomotopyTriangleComparison
/-!
概要：元終域の四補正道を、選択済み二変形と元入力固定で相対比較する。
方針：指定三辺を変えず、実入力射影の自明 Kan 性で二次元全体を持ち上げる。
規約：元入力・全三辺の代表を保持する。使われ方：共有四面体と対角境界の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
def dgGluingTargetCylinderHomotopy {A B : SSet.{u}} (V : A ⊗ Δ[1] ⟶ B) :
    SSet.Homotopy (ι₀ ≫ V) (ι₁ ≫ V) where
  h := V
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetPreCollarSpanHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y)
      (dgGluingHomTargetArrowFirstInputLift R C D E p q X Y) :=
  stableHomotopyRetarget
    (dgGluingTargetCylinderHomotopy (dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y))
    rfl (dgGluingHomTargetPreNormalizationInputPath_one R C D E p q X Y)

def dgGluingHomTargetPreCapSpanHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y)
      (dgGluingHomTargetStandardFirstInputLift R C D E p q X Y) :=
  stableHomotopyRetarget
    (dgGluingTargetCylinderHomotopy (dgGluingHomTargetPreCapInputPath R C D E p q X Y))
    (dgGluingHomTargetPreCapInputPath_zero R C D E p q X Y)
    (dgGluingHomTargetPreCapInputPath_one R C D E p q X Y)

def dgGluingHomTargetExitCollarSpanHomotopy :
    SSet.Homotopy (dgGluingHomTargetArrowLastInputLift R C D E p q X Y)
      (ι₁ ≫ dgGluingHomTargetExitCollarInputPath R C D E p q X Y) :=
  stableHomotopyRetarget
    (dgGluingTargetCylinderHomotopy (dgGluingHomTargetExitCollarInputPath R C D E p q X Y))
    (dgGluingHomTargetExitCollarInputPath_zero R C D E p q X Y) rfl

def dgGluingHomTargetExitCapSpanHomotopy :
    SSet.Homotopy (dgGluingHomTargetStandardLastInputLift R C D E p q X Y)
      (ι₁ ≫ dgGluingHomTargetExitCollarInputPath R C D E p q X Y) :=
  stableHomotopyRetarget
    (dgGluingTargetCylinderHomotopy (dgGluingHomTargetExitCapInputPath R C D E p q X Y))
    (dgGluingHomTargetExitCapInputPath_zero R C D E p q X Y)
    (dgGluingHomTargetExitCapInputPath_one R C D E p q X Y)

lemma dgGluingHomTargetPreCollarSpanHomotopy_over :
    (dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y).h ≫
      dgGluingHomTargetFirstInputProjection R C D E p q X Y =
    fst P (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) :=
  dgGluingHomTargetPreNormalizationInputPath_over R C D E p q X Y

lemma dgGluingHomTargetPreCapSpanHomotopy_over :
    (dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y).h ≫
      dgGluingHomTargetFirstInputProjection R C D E p q X Y =
    fst P (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) :=
  dgGluingHomTargetPreCapInputPath_over R C D E p q X Y

lemma dgGluingHomTargetExitCollarSpanHomotopy_over :
    (dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y).h ≫
      dgGluingHomTargetLastInputProjection R C D E p q X Y =
    fst P (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) :=
  dgGluingHomTargetExitCollarInputPath_over R C D E p q X Y

lemma dgGluingHomTargetExitCapSpanHomotopy_over :
    (dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y).h ≫
      dgGluingHomTargetLastInputProjection R C D E p q X Y =
    fst P (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) :=
  dgGluingHomTargetExitCapInputPath_over R C D E p q X Y

lemma dgGluingHomTargetFirstUnitSpan_relative_filling :
    ∃ T : (Δ[2] : SSet.{max (u + 1) v}) ⟶
        (ihom P).obj (dgGluingHomTargetFirstInputFiber R C D E p q X Y),
      (boundary 2).ι ≫ T = dgGluingHomotopyTriangleBoundary
        (dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y)
        (dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)
        (dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y) ∧
      T ≫ (ihom P).map (dgGluingHomTargetFirstInputProjection R C D E p q X Y) =
        SSet.const (functorVertex
          (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y))) := by
  let := dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  exact dgGluingInputHomotopyTriangle_relative_filling
    (dgGluingHomTargetFirstInputProjection R C D E p q X Y)
    (dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)
    (dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y)
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y))
    (dgGluingHomTargetPreCollarSpanHomotopy_over R C D E p q X Y)
    (dgGluingHomTargetFirstInputHomotopy_over R C D E p q X Y)
    (dgGluingHomTargetPreCapSpanHomotopy_over R C D E p q X Y)

lemma dgGluingHomTargetLastUnitSpan_relative_filling :
    ∃ T : (Δ[2] : SSet.{max (u + 1) v}) ⟶
        (ihom P).obj (dgGluingHomTargetLastInputFiber R C D E p q X Y),
      (boundary 2).ι ≫ T = dgGluingHomotopyTriangleBoundary
        (dgGluingHomTargetLastInputHomotopy R C D E p q X Y)
        (dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y)
        (dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y) ∧
      T ≫ (ihom P).map (dgGluingHomTargetLastInputProjection R C D E p q X Y) =
        SSet.const (functorVertex
          (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y))) := by
  let := dgGluingHomTargetLastInputProjection_trivialKanFibration R C D E p q X Y
  exact dgGluingInputHomotopyTriangle_relative_filling
    (dgGluingHomTargetLastInputProjection R C D E p q X Y)
    (dgGluingHomTargetLastInputHomotopy R C D E p q X Y)
    (dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y)
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y))
    (dgGluingHomTargetLastInputHomotopy_over R C D E p q X Y)
    (dgGluingHomTargetExitCapSpanHomotopy_over R C D E p q X Y)
    (dgGluingHomTargetExitCollarSpanHomotopy_over R C D E p q X Y)

end SerrePositivity.InfinityCategories
