module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFiniteRoofComposition
public import SerrePositivity.InfinityCategories.Derived.RoofHomotopyComposition
/-!
概要：元の実屋根の合成候補から、入力商 Hom 二族の実 AW 合成への実比較を構成する。
方針：指定商評価への比較と商内の合成評価の同定を、実二三角形のまま貼る。
規約：同時細分・三評価族・両比較と合成三角形を保持する。使われ方：任意標的の三作用族。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x y z : D) {K : SSet.{max u v}}
variable (r : K ⟶ dgRoofCorrespondence A D P x y) (s : K ⟶ dgRoofCorrespondence A D P y z)
variable (C : DGInvertingFiniteRoofComposition A D P x y z (dgQuotientNerveProjection A D P) r s)
variable (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))
variable (c : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj y) ((DGQuotient.inclusion A D P).obj z))
/-- 指定商評価を経由する、実合成候補から実 AW 合成への全パラメータ実比較。 -/
structure DGQuotientCompositeRealization where
  evaluation : DGInvertingRoofFamilyRealization A D P x z (dgQuotientNerveProjection A D P)
    C.source.compositeDenominator C.source.compositeNumerator C.composite
  valueHomotopy : SSet.Homotopy
    (dgQuotientFamilyEvaluationValue A D P x z C.source.compositeDenominator
      C.source.compositeNumerator C.composite) (pinchedHomCompositionFamily b c)
  comparison : SSet.Homotopy
    (C.source.compositeDiagram ≫ dgRoofCorrespondenceMap A D P x z)
    (pinchedHomCompositionFamily b c ≫ dgQuotientFixedHomRoofMap A D P x z)
  triangle : FunctorCompositionTriangle
    (dgQuotientFamilyEvaluationHomotopy A D P x z C.source.compositeDenominator
      C.source.compositeNumerator C.composite evaluation)
    (functorHomotopyPostcomp valueHomotopy (dgQuotientFixedHomRoofMap A D P x z)) comparison
/-- 指定入力の商側比較と同時細分に、実 AW 合成への二比較と実合成三角形が存在する。 -/
lemma dgQuotientCompositeRealization_nonempty (hP : DGQuotient.localKFlat A D P)
    (Hr : SSet.Homotopy (r ≫ dgRoofCorrespondenceMap A D P x y)
      (b ≫ dgQuotientFixedHomRoofMap A D P x y))
    (Hs : SSet.Homotopy (s ≫ dgRoofCorrespondenceMap A D P y z)
      (c ≫ dgQuotientFixedHomRoofMap A D P y z)) :
    Nonempty (DGQuotientCompositeRealization A D P x y z r s C b c) := by
  obtain ⟨E⟩ := dgInvertingRoofFamilyRealization_nonempty A D P x z
    (dgQuotientNerveProjection A D P) C.source.compositeDenominator
      C.source.compositeNumerator C.composite
  obtain ⟨H⟩ := dgQuotientCompositeEvaluation_homotopy A D P x y z r s C hP b c Hr Hs
  obtain ⟨J, ⟨T⟩⟩ := roofHomotopyComposition_exists
    (dgQuotientFamilyEvaluationHomotopy A D P x z C.source.compositeDenominator
      C.source.compositeNumerator C.composite E)
    (functorHomotopyPostcomp H (dgQuotientFixedHomRoofMap A D P x z))
  exact ⟨⟨E, H, J, T⟩⟩
end SerrePositivity.InfinityCategories
