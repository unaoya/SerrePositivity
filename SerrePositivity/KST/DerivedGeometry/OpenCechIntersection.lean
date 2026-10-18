module

public import SerrePositivity.KST.DerivedGeometry.OpenIntersectionProducts
public import SerrePositivity.KST.DerivedGeometry.CechFunctorComparison

/-!
概要：基本開との交叉後の族の Čech 複体と、切断を先に制限した Čech 複体の比較。
方針：非空な有限積の比較を Čech 対象の同型として束ね、前層で評価する。
規約：交叉の関手が空積を保つとは仮定しない。
使われ方：TT §3、Toën §3.2 の局所化後の有限基本開 Čech 複体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w c d a b
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry

/--
概要：関手を形式的余積の各成分へ適用する。
方針：添字を保持し、対象と各成分の射に同じ関手を適用する。
規約：関手の余極限保存は要求しない。
使われ方：TT §3、Toën §3.2 の交叉による Čech 対象の比較。
-/
def formalCoproductMapFunctor {C : Type c} [Category.{v} C]
    {D : Type d} [Category.{w} D] (F : C ⥤ D) :
    FormalCoproduct.{u} C ⥤ FormalCoproduct.{u} D where
  obj X := ⟨X.I, fun i => F.obj (X.obj i)⟩
  map f := ⟨f.f, fun i => F.map (f.φ i)⟩
  map_id _ := by
    refine FormalCoproduct.hom_ext rfl ?_
    intro i
    simp
  map_comp f g := by
    refine FormalCoproduct.hom_ext rfl ?_
    intro i
    simp

variable {R : CommRingCat.{u}} (a : R) {ι : Type v} (U : ι → (Spec R).Opens)

/--
概要：Čech の各交叉に D(a) を交叉させる対象と、交叉後の族の Čech 対象は同型。
方針：添字の恒等同値と非空な積の比較同型を使う。
規約：余面・退化の自然性を同時に検証する。
使われ方：TT §3、Toën §3.2 の基本開局所化後の Čech 計算。
-/
def basicOpenIntersectionCechIso :
    (FormalCoproduct.mk ι U).cech ⋙ formalCoproductMapFunctor (basicOpenIntersectionFunctor a) ≅
      (FormalCoproduct.mk ι (fun i => U i ⊓ basicOpen a)).cech :=
  NatIso.ofComponents
    (fun _ => FormalCoproduct.isoOfComponents (Equiv.refl _) (fun i =>
      PreservesProduct.iso (basicOpenIntersectionFunctor a) (U ∘ i)))
    (by
      intros n m f
      exact FormalCoproduct.hom_ext rfl (fun _ => Subsingleton.elim _ _))

/--
概要：切断を D(a) との交叉に制限した Čech 複体は交叉後の族の Čech 複体と同型。
方針：形式的 Čech 対象の交叉比較を対圏へ移し、同じ前層で評価する。
規約：符号・微分を含む複体同型。
使われ方：TT §3、Toën §3.2 の局所化後の Čech 収縮。
-/
def basicOpenIntersectionCechComplexIso {A : Type a} [Category.{b} A] [Preadditive A]
    [HasProducts.{v} A] (P : ((Spec R).Opens)ᵒᵖ ⥤ A) :
    (cechComplexFunctor U).obj ((basicOpenIntersectionFunctor a).op ⋙ P) ≅
      (cechComplexFunctor (fun i => U i ⊓ basicOpen a)).obj P :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso
    (Functor.isoWhiskerRight
      ((simplicialCosimplicialEquiv _).functor.mapIso (basicOpenIntersectionCechIso a U).op)
      ((FormalCoproduct.evalOp ((Spec R).Opens) A).obj P)).symm

end SerrePositivity.KST.DerivedGeometry
