module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCech

/-!
概要：係数前層から有限交叉の図式と Čech 複体への加法的関手。
方針：既存の係数写像の成分式を、関手の恒等・合成・加法の保存にまとめる。
規約：被覆を固定し、係数前層だけを変える。
使われ方：二重 Čech の縦微分の二乗の零と、零番の行の自然同型。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable {ι : Type} [DecidableEq ι] (U : ι → Opens X)

/-- 前層から有限交叉の係数図式への関手。 -/
def openCoverCechDiagramFunctor :
    ((Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) ⥤ (Finset ι ⥤ ModuleCat.{v} R) where
  obj P := openCoverCechDiagram P U
  map η := openCoverCechCoefficientMap η U
  map_id _ := by ext T; rfl
  map_comp _ _ := by ext T; rfl

/-- 有限交叉への制限は、係数の射の加法を保つ。 -/
instance openCoverCechDiagramFunctorAdditive : (openCoverCechDiagramFunctor (R := R) U).Additive where
  map_add {P Q f g} := by ext T x; rfl

/-- 全タプル Čech 複体の係数関手は、射の加法を保つ。 -/
instance fullCechComplexFunctorAdditive :
    (fullCechComplexFunctor (R := R) (ι := ι) :
      (Finset ι ⥤ ModuleCat.{v} R) ⥤ CochainComplex (ModuleCat.{v} R) ℕ).Additive where
  map_add {D E f g} := by ext q x t; rfl

/-- 前層から被覆の通常の Čech 複体への関手。 -/
def openCoverCechFunctor :
    ((Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  openCoverCechDiagramFunctor U ⋙ fullCechComplexFunctor

/-- 前層から Čech 複体への関手は加法的。 -/
instance openCoverCechFunctorAdditive : (openCoverCechFunctor (R := R) U).Additive := by
  dsimp only [openCoverCechFunctor]
  infer_instance

end SerrePositivity.AlgebraicGeometry
