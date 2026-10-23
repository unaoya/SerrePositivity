module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassMap
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroSourceModelHomotopy

/-!
概要：class 模型の全経路の後合成式と、逆経路合成の線形式を公開する。
方針：元の乗法的経路の全射式を underlying 複体で計算する。
規約：元の係数射・経路と後合成射を保持。使われ方：source 模型経路の終点比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants

namespace SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {N : Bimod A A}
  {q : W ⟶ A} {a b c : W ⟶ SquareZero.algebra A N}

lemma reverse_comp_hom_linear (v : SquareZero.RelativeWitness q N a b)
    (p : SquareZero.RelativeWitness q N a c) : (v.reverse.comp p).hom.hom =
      (b ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom - v.hom.hom + p.hom.hom := by
  rw [comp_hom_linear, reverse_hom_linear]
  abel

end SquareZero.RelativeWitness

namespace SquareZeroExtension
variable {R : Type u} [CommRing R] {A W C : Mon (Complex R)} {M N : Bimod A A}
  (m : M ⟶ N) (a : W ⟶ SquareZero.algebra A M) (b : W ⟶ SquareZero.algebra A N)
  {q : W ⟶ A} (v : SquareZero.RelativeWitness q N (a ≫ SquareZero.coefficientMap A m) b)

lemma classModelMap_path_post_linear (k : SquareZero.algebra A N ⟶ C) :
    ((classModelMap m a b v ≫ relativePath N b) ≫ DGAlgebra.Path.map R k).hom =
      (relativeLeft M a ≫ b ≫ k ≫ DGAlgebra.Path.diagonal R C).hom -
      (relativeLeft M a ≫ v.hom ≫ DGAlgebra.Path.map R k).hom +
      (relativePath M a ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A m ≫ k)).hom := by
  rw [Mon.comp_hom', classModelMap_path_linear]
  simp only [add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    DGAlgebra.Path.diagonal_naturality, ← DGAlgebra.Path.map_comp]

variable {B : Mon (Complex R)} (K : Bimod B B)
  (k : SquareZero.algebra A N ⟶ SquareZero.algebra B K)
  {q' : relativeModel M a ⟶ B}
  {x y z : relativeModel M a ⟶ SquareZero.algebra B K}
  (w : SquareZero.RelativeWitness q' K x y) (p : SquareZero.RelativeWitness q' K x z)

lemma classModelMap_path_post_of_witness
    (hb : relativeLeft M a ≫ b ≫ k = y)
    (hv : relativeLeft M a ≫ v.hom ≫ DGAlgebra.Path.map R k = w.hom)
    (hp : relativePath M a ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A m ≫ k) = p.hom) :
    (w.reverse.comp p).hom =
      (classModelMap m a b v ≫ relativePath N b) ≫ DGAlgebra.Path.map R k := by
  apply Mon.Hom.ext
  rw [SquareZero.RelativeWitness.reverse_comp_hom_linear, classModelMap_path_post_linear]
  rw [reassoc_of% hb, hv, hp]

variable {D : Mon (Complex R)} (K : Bimod A A) (f : D ⟶ SquareZero.algebra A K)
  (r : W ⟶ A) {l₀ l₁ : W ⟶ D} (h : DGAlgebra.Path.Witness R l₀ l₁)
  (hh : (h.postcomp f).hom ≫ DGAlgebra.Path.map R (SquareZero.projection A K) =
    r ≫ DGAlgebra.Path.diagonal R A)

lemma sourceModelClassWitness_hom : (sourceModelClassWitness K f r h hh).hom =
    h.hom ≫ DGAlgebra.Path.map R f := rfl

end SquareZeroExtension
end SerrePositivity.KST.LocalizingInvariants
