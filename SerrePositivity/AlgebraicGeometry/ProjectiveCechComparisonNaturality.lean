module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComparison
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：有界な Čech 複体と全タプル版とのコホモロジー比較は係数図式に対して自然。
方針：成分射影の自然変換へコホモロジー関手を適用する。
規約：被覆の添字集合を固定する。
使われ方：有限斉次表示の連結写像と、2g の係数図式の比較に使う。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

variable {R ι : Type*} [CommRing R] [LinearOrder ι]

/-- 有界版と全タプル版の Čech コホモロジー比較は、係数の自然変換と可換。 -/
def fullCechOrderedHomologyNatIso (q : ℕ) :
    fullCechComplexFunctor (R := R) (ι := ι) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q ≅
      orderedCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q :=
  NatIso.ofComponents (fun D ↦ fullCechOrderedHomologyIso D q) (by
    intro D E f
    exact (Functor.whiskerRight fullCechComplexRestrictOrderedNatTrans
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q)).naturality f)

end SerrePositivity.AlgebraicGeometry
