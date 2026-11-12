module
public import SerrePositivity.KST.NonConnective.DGKappaNativeSquareComparison
public import SerrePositivity.KST.Fibration.SpectrumSpaceEvaluation
/-!
概要：同じ未完備 D-9 四角形の新 coherent BF 四辺と旧 BF 射との指定比較を保持する。
方針：同じ四頂点の新四辺、正段の全辺比較・全四角形比較、整数 π 作用の一致を分ける。
規約：ユーザー採用の K-S•-S3 型変更。旧 BF 辺との厳密等式や Sp 写像空間内比較は要求しない。
使われ方：K-B の有限 BF 利用側と旧 kSpectrumMap による共終性界面の接続。
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
local instance nativeBFBoundarySpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

set_option maxHeartbeats 800000 in
-- 同じ D-9 の依存する四 BF 対象を全境界・正段比較で照合する構造宣言に限る。
/-- 概要：同じ未完備実列に限る新 coherent BF 四角形の明示供給データ。
方針：新四辺の実射と正段の指定比較・整数 π 作用の一致を保持する。
規約：存在は主張せず、旧射との厳密等式や一般 K 関手化を要求しない。
使われ方：採用済み有限 BF 供給命題のデータ部分。 -/
structure DGKappaNativeBFBoundaryInput where
  /-- 概要：同じ四角形の新しい bottom BF 射。
  方針：同じ二つの元の BF 頂点間の射として受け取る。
  規約：旧 kSpectrumMap との厳密等式は要求しない。
  使われ方：同じ coherent 四角形の実境界。 -/
  bottom : kOmegaSpectrum (stableCategoryModel (dgKappaNativeKernelCategory R D I)) ⟶
    kOmegaSpectrum (dgKappaNativeResolvedCone R D I)
  /-- 概要：新しい bottom 射と旧 BF 射の全正段の指定比較。
  方針：同じ正段空間値の全辺図式を比較する。
  規約：Sp 全写像空間の同型を仮定しない。
  使われ方：K-S•-S3 の元の正段比較を保持する。 -/
  bottom_positive : ∀ r : ℕ, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge bottom).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (kSpectrumMap (sInputExactMap (dgKappaNativeVerdierDiagram R D I).inclusion))).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))))
  /-- 概要：同じ bottom BF 射の全整数 π 作用は旧射と一致する。
  方針：元の同じ BF 群間の準同型の等式を受け取る。
  規約：辺や Sp の射の等式へ強めない。
  使われ方：旧 BF 群作用で述べた共終性との接続。 -/
  bottom_pi : ∀ j : ℤ, OmegaSpectrum.homotopyMap bottom j =
    OmegaSpectrum.homotopyMap (kSpectrumMap
      (sInputExactMap (dgKappaNativeVerdierDiagram R D I).inclusion)) j
  /-- 概要：同じ四角形の新しい right BF 射。
  方針：同じ二つの元の BF 頂点間の射として受け取る。
  規約：旧 kSpectrumMap との厳密等式は要求しない。
  使われ方：同じ coherent 四角形の実境界。 -/
  right : kOmegaSpectrum (dgKappaNativeResolvedCone R D I) ⟶
    kOmegaSpectrum (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))
  /-- 概要：新しい right 射と旧 BF 射の全正段の指定比較。
  方針：同じ正段空間値の全辺図式を比較する。
  規約：Sp 全写像空間の同型を仮定しない。
  使われ方：K-S•-S3 の元の正段比較を保持する。 -/
  right_positive : ∀ r : ℕ, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge right).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (kSpectrumMap (sInputExactMap (dgKappaNativeVerdierDiagram R D I).projection))).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))))
  /-- 概要：同じ right BF 射の全整数 π 作用は旧射と一致する。
  方針：元の同じ BF 群間の準同型の等式を受け取る。
  規約：辺や Sp の射の等式へ強めない。
  使われ方：旧 BF 群作用で述べた共終性との接続。 -/
  right_pi : ∀ j : ℤ, OmegaSpectrum.homotopyMap right j =
    OmegaSpectrum.homotopyMap (kSpectrumMap
      (sInputExactMap (dgKappaNativeVerdierDiagram R D I).projection)) j
  /-- 概要：同じ四角形の新しい left BF 射。
  方針：同じ二つの元の BF 頂点間の射として受け取る。
  規約：旧 kSpectrumMap との厳密等式は要求しない。
  使われ方：同じ coherent 四角形の実境界。 -/
  left : kOmegaSpectrum (stableCategoryModel (dgKappaNativeKernelCategory R D I)) ⟶
    kOmegaSpectrum (stableCategoryModel _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{max (u + 1) v})
  /-- 概要：新しい left 射と旧 BF 射の全正段の指定比較。
  方針：同じ正段空間値の全辺図式を比較する。
  規約：Sp 全写像空間の同型を仮定しない。
  使われ方：K-S•-S3 の元の正段比較を保持する。 -/
  left_positive : ∀ r : ℕ, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge left).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (kSpectrumMap (sInputExactMap
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (dgKappaNativeVerdierDiagram R D I).left)))).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))))
  /-- 概要：同じ left BF 射の全整数 π 作用は旧射と一致する。
  方針：元の同じ BF 群間の準同型の等式を受け取る。
  規約：辺や Sp の射の等式へ強めない。
  使われ方：旧 BF 群作用で述べた共終性との接続。 -/
  left_pi : ∀ j : ℤ, OmegaSpectrum.homotopyMap left j =
    OmegaSpectrum.homotopyMap (kSpectrumMap
      (sInputExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (dgKappaNativeVerdierDiagram R D I).left))) j
  /-- 概要：同じ四角形の新しい top BF 射。
  方針：同じ二つの元の BF 頂点間の射として受け取る。
  規約：旧 kSpectrumMap との厳密等式は要求しない。
  使われ方：同じ coherent 四角形の実境界。 -/
  top : kOmegaSpectrum (stableCategoryModel _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{max (u + 1) v}) ⟶
    kOmegaSpectrum (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))
  /-- 概要：新しい top 射と旧 BF 射の全正段の指定比較。
  方針：同じ正段空間値の全辺図式を比較する。
  規約：Sp 全写像空間の同型を仮定しない。
  使われ方：K-S•-S3 の元の正段比較を保持する。 -/
  top_positive : ∀ r : ℕ, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge top).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (kSpectrumMap (sInputExactMap
        (fromZeroCategory (dgKappaNativeVerdierDiagram R D I).right)))).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))))
  /-- 概要：同じ top BF 射の全整数 π 作用は旧射と一致する。
  方針：元の同じ BF 群間の準同型の等式を受け取る。
  規約：辺や Sp の射の等式へ強めない。
  使われ方：旧 BF 群作用で述べた共終性との接続。 -/
  top_pi : ∀ j : ℤ, OmegaSpectrum.homotopyMap top j =
    OmegaSpectrum.homotopyMap (kSpectrumMap
      (sInputExactMap (fromZeroCategory (dgKappaNativeVerdierDiagram R D I).right))) j
  /-- 概要：同じ新四辺を持つ実 coherent BF 四角形。
  方針：一つの全四角形を明示供給する。
  規約：存在は主張せず、元の実列に限る。
  使われ方：未完備 S• fibration から実 fiber 比較への接続。 -/
  square : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ Sp.{max (u + 1) v}
  /-- 概要：bottom 境界は同じ新 coherent BF 射そのもの。
  方針：元の全一単体の厳密回収を保持する。
  規約：旧 BF 射との等式ではない。
  使われ方：同じ実四角形の境界・頂点回収。 -/
  bottom_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge bottom).edge
  /-- 概要：right 境界は同じ新 coherent BF 射そのもの。
  方針：元の全一単体の厳密回収を保持する。
  規約：旧 BF 射との等式ではない。
  使われ方：同じ実四角形の境界・頂点回収。 -/
  right_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge right).edge
  /-- 概要：left 境界は同じ新 coherent BF 射そのもの。
  方針：元の全一単体の厳密回収を保持する。
  規約：旧 BF 射との等式ではない。
  使われ方：同じ実四角形の境界・頂点回収。 -/
  left_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge left).edge
  /-- 概要：top 境界は同じ新 coherent BF 射そのもの。
  方針：元の全一単体の厳密回収を保持する。
  規約：旧 BF 射との等式ではない。
  使われ方：同じ実四角形の境界・頂点回収。 -/
  top_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge top).edge
  /-- 概要：同じ新 BF 四角形の全正段は元の境界商の全四角形と比較される。
  方針：同じ指定二胞体を含む全図式比較を受け取る。
  規約：四辺の比較や π の等式だけで代用しない。
  使われ方：K-6 の全 S• 引き戻しを BF 正段へ渡す。 -/
  positive : ∀ r : ℕ, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
    ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor.{max (u + 1) v} r)))

end SerrePositivity.KST.NonConnective
