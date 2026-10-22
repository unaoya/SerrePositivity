module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeExtension
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeHomotopyPullbackExt

/-!
概要：同じ底の class 経路から、相対拡大模型間の実代数射を構成する。
方針：逆 class 経路と元の模型の経路を同じ源上で合成して、相対模型へ持ち上げる。
規約：元の両脚と経路の線形公式を保持。使われ方：実 class 模型の比較同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  {q : W ⟶ A} {a b : W ⟶ SquareZero.algebra A N} (v : SquareZero.RelativeWitness q N a b)

def transportWitness : SquareZero.RelativeWitness (relativeLeft N a ≫ q) N
    (relativeLeft N a ≫ b) (relativeRight N a ≫ SquareZero.zeroSection A N) :=
  (v.precomp (relativeLeft N a)).reverse.comp
    ((relativeWitness N a).rebase (by rw [v.source_projection]))

def transport : relativeModel N a ⟶ relativeModel N b :=
  DGAlgebra.RelativeHomotopyPullback.lift R (SquareZero.projection A N) b
    (SquareZero.zeroSection A N) (relativeLeft N a) (relativeRight N a)
    (transportWitness N v).toWitness (by
      simpa only [Category.assoc, v.target_projection] using (transportWitness N v).projection_eq)

lemma transport_left : transport N v ≫ relativeLeft N b = relativeLeft N a :=
  DGAlgebra.RelativeHomotopyPullback.lift_left R _ _ _ _ _ _ _

lemma transport_right : transport N v ≫ relativeRight N b = relativeRight N a :=
  DGAlgebra.RelativeHomotopyPullback.lift_right R _ _ _ _ _ _ _

lemma transport_path : transport N v ≫ relativePath N b = (transportWitness N v).hom :=
  DGAlgebra.RelativeHomotopyPullback.lift_path R _ _ _ _ _ _ _

lemma transport_path_linear : (transport N v ≫ relativePath N b).hom =
    (relativeLeft N a ≫ b ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom -
      (relativeLeft N a ≫ v.hom).hom + (relativePath N a).hom := by
  rw [transport_path]
  change (((v.precomp (relativeLeft N a)).reverse).comp _).hom.hom = _
  rw [SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.reverse_hom_linear]
  change ((relativeLeft N a ≫ a) ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom -
      (relativeLeft N a ≫ v.hom).hom +
      ((relativeLeft N a ≫ b) ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom -
      ((relativeLeft N a ≫ a) ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom +
      (relativePath N a).hom = _
  simp only [Category.assoc]
  abel

lemma transport_path_linear_precomp {T : Mon (Complex R)} (m : T ⟶ relativeModel N a) :
    ((m ≫ transport N v) ≫ relativePath N b).hom =
      (m ≫ relativeLeft N a ≫ b ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom -
        (m ≫ relativeLeft N a ≫ v.hom).hom + (m ≫ relativePath N a).hom := by
  have h := congrArg (fun t => m.hom ≫ t) (transport_path_linear N v)
  simpa only [Mon.comp_hom', comp_add, comp_sub, Category.assoc] using h

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
