module

public import SerrePositivity.EInfinity.ComplexLimits.CofibrantHomQuillen
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedMonomorphismCofibration

/-!
# cofibrant 複体の実テンソルの左 Quillen 性

概要：元の cofibrant X を左にテンソルする関手は実射影 left Quillen。
方針：同じ閉随伴と構成した Hom の right Quillen 性を使う。
規約：任意可換環上の非有界複体に適用する。
使われ方：正規化した全単射・標準境界のテンソル像の cofibration 性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma tensorLeft_cofibrant_isLeftQuillen (X : Complex A)
    (hX : (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ X)) :
    letI := projectiveModelCategory A
    SerrePositivity.Quillen.IsLeftQuillen (tensorLeft X) := by
  let := projectiveModelCategory A
  have : SerrePositivity.Quillen.IsRightQuillen (ihom X) :=
    homFunctor_cofibrant_isRightQuillen X hX
  exact SerrePositivity.Quillen.isLeftQuillen_of_isRightQuillen (ihom.adjunction X)

lemma normalizedTensorMonomorphism_cofibration (X : Complex A)
    (hX : (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ X)) {S T : SSet.{0}} (f : S ⟶ T) [Mono f] :
    (projectiveGeneratingCofibrations A).rlp.llp
      (X ◁ (BarrattEccles.normalizedFunctor A).map f) := by
  let := projectiveModelCategory A
  have := tensorLeft_cofibrant_isLeftQuillen X hX
  exact SerrePositivity.Quillen.IsLeftQuillen.map_cofibrations
    (L := tensorLeft X) _ (normalizedMonomorphism_cofibration A f)

end SerrePositivity.EInfinity.ComplexLimits
