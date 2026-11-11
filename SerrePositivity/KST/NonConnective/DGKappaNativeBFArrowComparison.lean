module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFSquare

/-!
概要：同じ新 coherent BF 四辺と旧 kSpectrumMap の指定比較・整数 π 一致を消費する。
方針：同じ四辺だけを添字付け、旧共終性の結論を同じ整数 π の等式で移す。
規約：旧辺との厳密等式や Sp 写像空間内比較、実商射の完備化性は主張しない。
使われ方：K-S•-S3 の新四辺と旧 K-cof 供給の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance nativeBFArrowSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hBF : dgKappaNativeBFSquareComparison R D I)

/-- 概要：同じ未完備四角形の下・右・左・上の元の完全射を添字付ける。
方針：同じ元の四つの sInputExactMap を Arrow に束ねる。
規約：一般の完全射に対する新しい K 作用ではない。
使われ方：同じ四辺の共終性・整数 π 作用の旧界面。 -/
def dgKappaNativeBFOldArrow : Fin 4 → Arrow (StableModel.{max (u + 1) v}) :=
  Fin.cases (Arrow.mk (sInputExactMap (dgKappaNativeVerdierDiagram R D I).inclusion))
    (Fin.cases (Arrow.mk (sInputExactMap (dgKappaNativeVerdierDiagram R D I).projection))
      (Fin.cases (Arrow.mk (sInputExactMap
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (dgKappaNativeVerdierDiagram R D I).left)))
        (Fin.cases (Arrow.mk (sInputExactMap
          (fromZeroCategory (dgKappaNativeVerdierDiagram R D I).right))) Fin.elim0)))

/-- 概要：同じ四辺の新 coherent BF 射を元の二つの BF 対象の間で読む。
方針：同じ供給データの下・右・左・上の射を取り出す。
規約：旧 kSpectrumMap との等式を入力しない。
使われ方：元の BF 群を保つ正段比較と整数 π 作用。 -/
def dgKappaNativeBFArrow (e : Fin 4) :
    kOmegaSpectrum (dgKappaNativeBFOldArrow R D I e).left ⟶
      kOmegaSpectrum (dgKappaNativeBFOldArrow R D I e).right :=
  Fin.cases (dgKappaNativeBFBoundary R D I hBF).bottom
    (Fin.cases (dgKappaNativeBFBoundary R D I hBF).right
      (Fin.cases (dgKappaNativeBFBoundary R D I hBF).left
        (Fin.cases (dgKappaNativeBFBoundary R D I hBF).top (fun i => Fin.elim0 i)))) e

/-- 概要：同じ新 coherent BF 辺と旧 BF 辺の各正段の指定全図式比較。
方針：同じ四辺の指定比較を一つの添字付き族へ束ねる。
規約：Sp 全写像空間の関手同型に強めない。
使われ方：K-S•-S3 の元の各正段比較を保持する。 -/
def dgKappaNativeBFArrowPositiveComparison (e : Fin 4) (r : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFArrow R D I hBF e)).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
    (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kSpectrumMap (dgKappaNativeBFOldArrow R D I e).hom)).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))) :=
  Classical.choice (by
    fin_cases e
    · exact (dgKappaNativeBFBoundary R D I hBF).bottom_positive r
    · exact (dgKappaNativeBFBoundary R D I hBF).right_positive r
    · exact (dgKappaNativeBFBoundary R D I hBF).left_positive r
    · exact (dgKappaNativeBFBoundary R D I hBF).top_positive r)

/-- 概要：同じ新 coherent BF 四辺の全整数 π 作用は旧 BF 射と一致する。
方針：同じ元の BF 群の準同型の等式を添字付きで回収する。
規約：辺の等号や Sp 全写像空間内の同型を結論しない。
使われ方：旧 kSpectrumMap の整数 π で述べた K-cof の消費。 -/
theorem dgKappaNativeBFArrow_homotopyMap_eq (e : Fin 4) (j : ℤ) :
    OmegaSpectrum.homotopyMap (dgKappaNativeBFArrow R D I hBF e) j =
      OmegaSpectrum.homotopyMap (kSpectrumMap (dgKappaNativeBFOldArrow R D I e).hom) j := by
  fin_cases e
  · exact (dgKappaNativeBFBoundary R D I hBF).bottom_pi j
  · exact (dgKappaNativeBFBoundary R D I hBF).right_pi j
  · exact (dgKappaNativeBFBoundary R D I hBF).left_pi j
  · exact (dgKappaNativeBFBoundary R D I hBF).top_pi j

/-- 概要：旧 K-cof の正次数全単射・零次単射は同じ新 BF 辺へ整数 π の一致で移る。
方針：旧射に共終性を適用し、同じ群準同型の等式だけで結論を読み替える。
規約：元の完全射の完備化性に条件付きで、実商射の完備化性は主張しない。
使われ方：K-S•-S3 の新 BF 辺と旧共終性界面の接続。 -/
theorem dgKappaNativeBFArrow_cofinal
    (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
        (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
          Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
    (e : Fin 4)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (dgKappaNativeBFOldArrow R D I e).hom.val) :
    (∀ j : ℤ, 0 < j → Function.Bijective
      (OmegaSpectrum.homotopyMap (dgKappaNativeBFArrow R D I hBF e) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (dgKappaNativeBFArrow R D I hBF e) 0) := by
  have h := hcofinal _ _ (dgKappaNativeBFOldArrow R D I e).hom hf
  constructor
  · intro j hj
    rw [dgKappaNativeBFArrow_homotopyMap_eq]
    exact h.1 j hj
  · rw [dgKappaNativeBFArrow_homotopyMap_eq]
    exact h.2

end SerrePositivity.KST.NonConnective
