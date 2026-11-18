module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.CofibrantHomQuillen
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedMonomorphismCofibration

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma tensorLeft_cofibrant_isLeftQuillen (X : Complex A)
    (hX : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ X)) :
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    SerrePositivity.Quillen.IsLeftQuillen (tensorLeft X) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have : SerrePositivity.Quillen.IsRightQuillen (ihom X) :=
    _root_.SerrePositivity.ComplexLimits.homFunctor_cofibrant_isRightQuillen X hX
  exact SerrePositivity.Quillen.isLeftQuillen_of_isRightQuillen (ihom.adjunction X)

lemma normalizedTensorMonomorphism_cofibration (X : Complex A)
    (hX : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ X)) {S T : SSet.{0}} (f : S ⟶ T) [Mono f] :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (X ◁ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ComplexLimits.tensorLeft_cofibrant_isLeftQuillen X hX
  exact SerrePositivity.Quillen.IsLeftQuillen.map_cofibrations
    (L := tensorLeft X) _ (_root_.SerrePositivity.ComplexLimits.normalizedMonomorphism_cofibration A f)

end SerrePositivity.ComplexLimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.2.11" (partial := component) "仮定：任意可換環 R の非有界複体と構成済み射影モデル構造（HA と一致）。結論：テンソル単位の cofibrancy と任意 cofibrant X による左テンソルの左 Quillen 性を示す（HA のモノイダル模型の結論の一部に一致）。任意の二つの cofibration の pushout-product 公理全体を登録した宣言は含まれない。"] _root_.SerrePositivity.ComplexLimits.tensorLeft_cofibrant_isLeftQuillen
