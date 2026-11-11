module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PullbackComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeKProjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # 標準 fiber による導来引き戻しの判定

概要：D(S) の四角形は頂点から標準 fiber への比較射が擬同型であるとき、かつそのときに限り引き戻し。
方針：semifree の K-projective 性から比較辺の可逆性を得て、右ファイブレーションと錐の同型不変性を使う。
規約：任意の可換環と非有界複体。使われ方：D4 の双方向の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded

open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 概要：semifree 複体間の擬同型を表す辺は可逆である。
方針：K-projective 複体間の擬同型はホモトピー同値であり、二つの充満忠実比較が同型を反映する。
規約：辺を全複体へ包含した鎖写像で擬同型性を述べる。使われ方：比較辺の可逆性。 -/
lemma derived_edge_invertible_of_quasiIso {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) x y)
    (he : QuasiIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (e.map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective S (x.obj 0).property
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective S (y.obj 0).property
  let a : (x.obj 0).val ⟶ (y.obj 0).val :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (e.map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))
  have hh := (CochainComplex.IsKProjective.quasiIso_iff a).mp he
  have hi := (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences _).mpr hh
  have hi' : IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).map
      (SSet.Truncated.HomotopyCategory₂.homMk e))) := hi
  have : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).map (SSet.Truncated.HomotopyCategory₂.homMk e)) :=
    isIso_of_reflects_iso _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S)
  have : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) :=
    isIso_of_reflects_iso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S))
  change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map
    (SSet.Truncated.HomotopyCategory₂.homMk e))
  infer_instance

private lemma invertible_transportTarget_iff {X : SSet.{u}} {x y z : X _⦋0⦌}
    (h : y = z) (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeTransportTarget h e) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  cases h
  rfl

private lemma rebase_limit_iff {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone h c) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  cases h
  rfl

/-- 概要：標準 fiber への比較射が擬同型なら、D(S) の四角形は引き戻しである。
方針：頂点の比較辺の可逆性を slice 射影で反映し、標準極限錐から同型不変性で移す。
規約：比較射は任意の四角形に既に定義されている。使われ方：D4 の十分条件。 -/
theorem derived_isPullbackSquare_of_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)
    (hF : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F := by
  have he := derived_edge_invertible_of_quasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonEdge F) hF
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonSliceEdge F).map
      ((SSet.truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F))))) :=
    (invertible_transportTarget_iff (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_vertex F) _).mp he
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonSliceEdge F) hp
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonCone F) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_isPullback F).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonSliceEdge F))).symm
  exact (rebase_limit_iff (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_cospan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)).mp hc

/-- 概要：D(S) の引き戻しは標準 fiber への比較射の擬同型性と同値である。
方針：N7 の極限の一意性による必要条件と、錐の同型不変性による十分条件を合わせる。
規約：可換環以外に追加の数学的仮定なし。使われ方：BS 界面の導来引き戻し判定。 -/
theorem derived_isPullbackSquare_iff_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison_quasiIso F, derived_isPullbackSquare_of_quasiIso F⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
