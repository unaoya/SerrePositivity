module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitInputEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitInputCoefficientEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.InputHomotopyTriangleComparison
/-! # 元入力を固定する実単位補正 span と選択済み二変形の相対比較

概要：四つの実補正道を正本入力 lift に接続し、選択済み二変形を含む指定三辺を充填する。
方針：実際の道を保ったまま端点の等式で型を合わせ、入力射影の自明 Kan 性を使う。
規約：三辺の代表と二次元全体の元 Hom 入力を厳密に保持する。
使われ方：augmentation 四面体の貼り合わせを選択済み二変形へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingPreCollarSpanHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingPreCollarModelInputPath R C D M X Y)
      (dgGluingLaxHomFirstCompositionInputLift R C D M X Y) :=
  stableHomotopyRetarget (dgGluingPreCollarModelInputHomotopy R C D M X Y)
    rfl (dgGluingPreCollarModelInputPath_one R C D M X Y)

lemma dgGluingPreCollarSpanHomotopy_h :
    (dgGluingPreCollarSpanHomotopy R C D M X Y).h =
      dgGluingPreCollarModelInputPath R C D M X Y := rfl

def dgGluingPreCapSpanHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingPreCollarModelInputPath R C D M X Y)
      (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y) :=
  stableHomotopyRetarget (dgGluingPreCapModelInputHomotopy R C D M X Y)
    (dgGluingPreCapModelInputPath_zero R C D M X Y)
    (dgGluingPreCapModelInputPath_one R C D M X Y)

lemma dgGluingPreCapSpanHomotopy_h :
    (dgGluingPreCapSpanHomotopy R C D M X Y).h =
      dgGluingPreCapModelInputPath R C D M X Y := rfl

def dgGluingExitCollarSpanHomotopy :
    SSet.Homotopy (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
      (ι₁ ≫ dgGluingExitCollarModelInputPath R C D M X Y) :=
  stableHomotopyRetarget (dgGluingExitCollarModelInputHomotopy R C D M X Y)
    (dgGluingExitCollarModelInputPath_zero R C D M X Y) rfl

lemma dgGluingExitCollarSpanHomotopy_h :
    (dgGluingExitCollarSpanHomotopy R C D M X Y).h =
      dgGluingExitCollarModelInputPath R C D M X Y := rfl

def dgGluingExitCapSpanHomotopy :
    SSet.Homotopy (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
      (ι₁ ≫ dgGluingExitCollarModelInputPath R C D M X Y) :=
  stableHomotopyRetarget (dgGluingExitCapModelInputHomotopy R C D M X Y)
    (dgGluingExitCapModelInputPath_zero R C D M X Y)
    (dgGluingExitCapModelInputPath_one R C D M X Y)

lemma dgGluingExitCapSpanHomotopy_h :
    (dgGluingExitCapSpanHomotopy R C D M X Y).h =
      dgGluingExitCapModelInputPath R C D M X Y := rfl

lemma dgGluingFirstUnitSpan_relative_filling :
    ∃ T : (Δ[2] : SSet.{max (u + 1) v w}) ⟶
        (ihom ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).obj
          (dgGluingDerivedFirstCompositionInputFiber R C D M X Y),
      (boundary 2).ι ≫ T = dgGluingHomotopyTriangleBoundary
        (dgGluingPreCollarSpanHomotopy R C D M X Y)
    (dgGluingLaxHomFirstInputHomotopy R C D M X Y)
        (dgGluingPreCapSpanHomotopy R C D M X Y) ∧
      T ≫ (ihom _).map (dgGluingDerivedFirstCompositionInputProjection R C D M X Y) =
        SSet.const (functorVertex ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)))) := by
  have := dgGluingDerivedFirstCompositionInputProjection_trivialKanFibration R C D M X Y
  apply dgGluingInputHomotopyTriangle_relative_filling
  · exact dgGluingPreCollarModelInputHomotopy_over R C D M X Y
  · exact dgGluingLaxHomFirstInputHomotopy_over R C D M X Y
  · exact dgGluingPreCapModelInputHomotopy_over R C D M X Y

lemma dgGluingLastUnitSpan_relative_filling :
    ∃ T : (Δ[2] : SSet.{max (u + 1) v w}) ⟶
        (ihom ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).obj
          (dgGluingDerivedLastCompositionInputFiber R C D M X Y),
      (boundary 2).ι ≫ T = dgGluingHomotopyTriangleBoundary
        (dgGluingLaxHomLastInputHomotopy R C D M X Y)
    (dgGluingExitCapSpanHomotopy R C D M X Y)
        (dgGluingExitCollarSpanHomotopy R C D M X Y) ∧
      T ≫ (ihom _).map (dgGluingDerivedLastCompositionInputProjection R C D M X Y) =
        SSet.const (functorVertex ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))) := by
  have := dgGluingDerivedLastCompositionInputProjection_trivialKanFibration R C D M X Y
  apply dgGluingInputHomotopyTriangle_relative_filling
  · exact dgGluingLaxHomLastInputHomotopy_over R C D M X Y
  · exact dgGluingExitCapModelInputHomotopy_over R C D M X Y
  · exact dgGluingExitCollarModelInputHomotopy_over R C D M X Y
end SerrePositivity.InfinityCategories
