module
public import SerrePositivity.InfinityCategories.Derived.PullbackComparison
public import SerrePositivity.InfinityCategories.Derived.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Derived.SemifreeKProjective
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open DGNerve.HomotopyComparison
open scoped Simplicial
variable {S : Type u} [CommRing S]

/-- 概要：semifree 複体間の擬同型を表す辺は可逆である。
方針：K-projective 複体間の擬同型はホモトピー同値であり、二つの充満忠実比較が同型を反映する。
規約：辺を全複体へ包含した鎖写像で擬同型性を述べる。使われ方：比較辺の可逆性。 -/
lemma derived_edge_invertible_of_quasiIso {x y : (derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := twoTruncation S (Semifree S)) x y)
    (he : QuasiIso (edgeChainMap (e.map ((SSet.truncation 2).map derivedInfinityInclusion)))) :
    IsInvertibleEdge e := by
  have := complexSemifree_isKProjective S (x.obj 0).property
  have := complexSemifree_isKProjective S (y.obj 0).property
  let a : (x.obj 0).val ⟶ (y.obj 0).val :=
    edgeChainMap (e.map ((SSet.truncation 2).map derivedInfinityInclusion))
  have hh := (CochainComplex.IsKProjective.quasiIso_iff a).mp he
  have hi := (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences _).mpr hh
  have hi' : IsIso ((semifreeHomotopyComparison S).map ((toH0 S (Semifree S)).map
      (SSet.Truncated.HomotopyCategory₂.homMk e))) := hi
  have : IsIso ((toH0 S (Semifree S)).map (SSet.Truncated.HomotopyCategory₂.homMk e)) :=
    isIso_of_reflects_iso _ (semifreeHomotopyComparison S)
  have : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) :=
    isIso_of_reflects_iso _ (toH0 S (Semifree S))
  change IsIso ((edgeToPathHomotopyCategory _).map
    (SSet.Truncated.HomotopyCategory₂.homMk e))
  infer_instance

private lemma invertible_transportTarget_iff {X : SSet.{u}} {x y z : X _⦋0⦌}
    (h : y = z) (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj X) x y) :
    IsInvertibleEdge (edgeTransportTarget h e) ↔ IsInvertibleEdge e := by
  cases h
  rfl

private lemma rebase_limit_iff {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    (c : JoinCone q) : IsLimitCone (rebaseCone h c) ↔ IsLimitCone c := by
  cases h
  rfl

/-- 概要：標準 fiber への比較射が擬同型なら、D(S) の四角形は引き戻しである。
方針：頂点の比較辺の可逆性を slice 射影で反映し、標準極限錐から同型不変性で移す。
規約：比較射は任意の四角形に既に定義されている。使われ方：D4 の十分条件。 -/
theorem derived_isPullbackSquare_of_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)
    (hF : QuasiIso (derivedSquareFiberComparison F)) : IsPullbackSquare F := by
  have he := derived_edge_invertible_of_quasiIso (derivedSquareComparisonEdge F) hF
  have hp : IsInvertibleEdge ((derivedSquareComparisonSliceEdge F).map
      ((SSet.truncation 2).map (sliceOverProjection
        (pullbackCospan (derivedSquareFiberSquare F))))) :=
    (invertible_transportTarget_iff (derivedSquareFiberSquare_vertex F) _).mp he
  have := derived_rightFibration_reflects_invertibleEdge
    (sliceOverProjection (pullbackCospan (derivedSquareFiberSquare F)))
    (derivedSquareComparisonSliceEdge F) hp
  have hc : IsLimitCone (derivedSquareComparisonCone F) :=
    (derivedSquareFiberSquare_isPullback F).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk (derivedSquareComparisonSliceEdge F))).symm
  exact (rebase_limit_iff (derivedSquareFiberSquare_cospan F) (pullbackCone F)).mp hc

/-- 概要：D(S) の引き戻しは標準 fiber への比較射の擬同型性と同値である。
方針：N7 の極限の一意性による必要条件と、錐の同型不変性による十分条件を合わせる。
規約：可換環以外に追加の数学的仮定なし。使われ方：BS 界面の導来引き戻し判定。 -/
theorem derived_isPullbackSquare_iff_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    IsPullbackSquare F ↔ QuasiIso (derivedSquareFiberComparison F) :=
  ⟨derivedSquareFiberComparison_quasiIso F, derived_isPullbackSquare_of_quasiIso F⟩

end SerrePositivity.InfinityCategories
