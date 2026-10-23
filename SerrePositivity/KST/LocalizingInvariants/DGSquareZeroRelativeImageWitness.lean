module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeExtension
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver

/-!
概要：元の相対模型の経路を、底変更と零切断を保つ実平方零射で写す。
方針：元の両評価と底射影を使い、右脚の値を基底とする相対証人にする。
規約：元の相対経路の全射を保持。使われ方：source 模型経路の実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A B W : Mon (Complex R)}
  (M : Bimod A A) (a : W ⟶ SquareZero.algebra A M) (q : A ⟶ B) (N : Bimod B B)
  (k : SquareZero.algebra A M ⟶ SquareZero.algebra B N)
  (hk : k ≫ SquareZero.projection B N = SquareZero.projection A M ≫ q)
  (hz : SquareZero.zeroSection A M ≫ k = q ≫ SquareZero.zeroSection B N)

def relativeImageWitness : SquareZero.RelativeWitness (relativeRight M a ≫ q) N
    (relativeLeft M a ≫ (a ≫ k)) ((relativeRight M a ≫ q) ≫ SquareZero.zeroSection B N) where
  hom := (relativeWitness M a).hom ≫ DGAlgebra.Path.map R k
  source_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_source, ← Category.assoc,
      (relativeWitness M a).source_eq, Category.assoc]
  target_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_target, ← Category.assoc,
      (relativeWitness M a).target_eq, Category.assoc, hz, ← Category.assoc]
  projection_eq := by
    have h := ((relativeWitness M a).mapOver q k hk).projection_eq
    change ((relativeWitness M a).hom ≫ DGAlgebra.Path.map R k) ≫
      DGAlgebra.Path.map R (SquareZero.projection B N) =
      ((relativeLeft M a ≫ a ≫ SquareZero.projection A M) ≫ q) ≫
        DGAlgebra.Path.diagonal R B at h
    exact h.trans (congrArg (fun t => (t ≫ q) ≫ DGAlgebra.Path.diagonal R B)
      (relativeRight_eq M a).symm)

lemma relativeImageWitness_hom : (relativeImageWitness M a q N k (hk := hk) (hz := hz)).hom =
    relativePath M a ≫ DGAlgebra.Path.map R k := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
