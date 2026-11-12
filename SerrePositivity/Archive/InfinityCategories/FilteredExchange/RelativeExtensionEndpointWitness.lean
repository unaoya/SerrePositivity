module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint

/-!
概要：元の相対延長と実際の終点を、指定比較の合成に必要な共通データで保持する。
方針：全延長・初期値・終点の厳密な式を束ね、既存の指定比較をそのまま使う。
規約：新しい比較は選択しない。使われ方：三単体の共有面の比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 共通の底・初期値を持ち、実際の終点を指定した相対延長。 -/
structure RelativeExtensionEndpointWitness {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) where
  extension : A ⟶ E
  over : extension ≫ p = b
  initial : i ≫ extension = v
  endpoint : C ⟶ pullback p q
  endpoint_over : endpoint ≫ pullback.snd p q = a
  evaluate : j ≫ extension = endpoint ≫ pullback.fst p q

variable {A D C E F B : SSet.{u}} {p : E ⟶ B} {b : A ⟶ B}
  {i : D ⟶ A} {v : D ⟶ E} {j : C ⟶ A} {q : F ⟶ B} {a : C ⟶ F}

/-- 証拠が表す、元の全相対延長空間の実際の頂点。 -/
def RelativeExtensionEndpointWitness.point (w : RelativeExtensionEndpointWitness p b i v j q a)
    (hv : v ≫ p = i ≫ b) : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨w.extension, w.over, w.initial⟩

/-- 二つの元の証拠の間の比較は、既存の同じ終点比較そのもの。 -/
def RelativeExtensionEndpointWitness.iso [LeftFibration p]
    (w w' : RelativeExtensionEndpointWitness p b i v j q a)
    (hi : leftAnodyneExtensions i) (hv : v ≫ p = i ≫ b) (hj : j ≫ b = a ≫ q) :
    VertexIso (relativeFunctorVertex (pullback.snd p q) a w.endpoint w.endpoint_over)
      (relativeFunctorVertex (pullback.snd p q) a w'.endpoint w'.endpoint_over) :=
  relativeFunctorExtensionEndpoint_witnessIso p b i hi v hv j q a hj
    w.extension w'.extension w.over w'.over w.initial w'.initial
    w.endpoint w'.endpoint w.endpoint_over w'.endpoint_over w.evaluate w'.evaluate

end SerrePositivity.InfinityCategories.F2
