module

public import SerrePositivity.AlgebraicGeometry.DegreeOneStandardOpen
public import SerrePositivity.AlgebraicGeometry.ReesScalarStructureMorphism

/-!
概要：実際の有限な次数一表示の証人を、同じ基底上の同型とともに束ねる。
方針：元の全射評価・次数分解・Proj の同型をそのまま保持する。
規約：モデルの存在や有限性を新しい仮定として最終の主張に加えない。
使われ方：Rees・Segre の表示を、実際の有限ファイバー冪へ帰納する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- 同じ Spec R 上の、有限な次数一評価による Proj の実際の表示の証人。 -/
structure DegreeOneProjectiveModel {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) where
  index : Type
  [indexFintype : Fintype index]
  [indexLinearOrder : LinearOrder index]
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra R ring]
  grade : ℕ → Submodule R ring
  [gradedRing : GradedRing grade]
  generator : index → ring
  homogeneous : ∀ i, generator i ∈ grade 1
  surjective : Function.Surjective (MvPolynomial.aeval (R := R) generator)
  iso : Y ≅ Proj grade
  over : iso.hom ≫ projectiveCechStructureMap grade = f

attribute [instance] DegreeOneProjectiveModel.indexFintype
  DegreeOneProjectiveModel.indexLinearOrder DegreeOneProjectiveModel.commRing
  DegreeOneProjectiveModel.algebra DegreeOneProjectiveModel.gradedRing

/-- 元の Proj の全射な次数一表示を、同じ構造射の証人として束ねる。 -/
def degreeOneProjectiveModelOfProj {R A : Type u} {ι : Type}
    [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [LinearOrder ι]
    (G : ℕ → Submodule R A) [GradedRing G] (a : ι → A)
    (ha : ∀ i, a i ∈ G 1) (hs : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    DegreeOneProjectiveModel (projectiveCechStructureMap G) where
  index := ι
  ring := A
  grade := G
  generator := a
  homogeneous := ha
  surjective := hs
  iso := Iso.refl _
  over := by simp

/-- 基底への同じ射を保つ、表示の同型による移送。 -/
def DegreeOneProjectiveModel.ofIso {R : Type u} [CommRing R] {Y Y' : Scheme.{u}}
    {f : Y ⟶ Spec (CommRingCat.of R)} (m : DegreeOneProjectiveModel f) (e : Y' ≅ Y) :
    DegreeOneProjectiveModel (e.hom ≫ f) where
  index := m.index
  ring := m.ring
  grade := m.grade
  generator := m.generator
  homogeneous := m.homogeneous
  surjective := m.surjective
  iso := e ≪≫ m.iso
  over := by simpa only [Iso.trans_hom, Category.assoc] using congrArg (e.hom ≫ ·) m.over

end SerrePositivity.AlgebraicGeometry
