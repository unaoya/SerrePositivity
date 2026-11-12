module
public import SerrePositivity.KST.NonConnective.DGKappaNativeVerdier
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOASpectrumComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFEvaluationComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionExact

/-!
概要：完備化前の同じ実商から、元の固定 K 値への実完備化比較を作る。
方針：元の dg Yoneda を始域の移送なしで認証し、同じ実 Perf 評価と SOA 比較を続ける。
規約：共終性を明示仮定引数に取る。固定 S・ν・K と実商は変更しない。
使われ方：K-7 c5・d3 の完備化前の fibration から同じ固定 K の構造辺への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance rawSuspensionCompletionSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "Q" => dgKappaSuspensionKInput R D I

/-- 概要：完備化前の同じ実商から出る元の dg Yoneda 自身が冪等完備化である。
方針：D 正本の代表加群 retract 表示と同じ全 Hom の充満忠実性を使う。
規約：元の実商の始域を保持し、完備化を同値とは扱わない。
使われ方：共終性引数を同じ実商に直接適用する。 -/
theorem dgKappaRawSuspensionYoneda_isIdempotentCompletion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q))) := by
  let := dgKappaSuspension_isDGPretriangulated R D I
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R (Q), ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso
    intro x y
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance
  · intro z
    obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
    obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectVertex_retract_yoneda R (Q) M
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x, ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    exact hx

/-- 概要：元の実商の dg Yoneda を同じ native 安定模型射として保持する。
方針：F2 正本の完備化の完全性を同じ認証に適用する。
規約：元の実商と元の Perf 値をそのまま使う。
使われ方：完備化前後の実 BF K 比較。 -/
def dgKappaRawSuspensionYonedaStableMap :
    stableCategoryModel (dgKappaNativeSuspensionCategory R D I) ⟶
      perfectDGStableModel R (Q) Set.univ := by
  let := (dgKappaRawSuspensionYoneda_isIdempotentCompletion R D I).isExactFunctor
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q)))
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q)), preservesCofiberData_of_isExactFunctor _⟩

/-- 概要：同じ実 Perf の native K から元の固定 K への実 BF 比較。
方針：元の実 Perf 評価同値の逆 K 射と元の SOA 比較を合成する。
規約：同じラベル評価の完全な逆を保持し、別の固定 K を定義しない。
使われ方：同じ実商の完備化比較の標的を固定 K へ戻す。 -/
def dgKappaSuspensionNativePerfectToFixed :
    kOmegaSpectrum (perfectDGStableModel R (Q) Set.univ) ⟶ dgKInputSpectrum R (Q) :=
  kSpectrumMap (presentedPerfectDGBFEvaluationEquivalence R (Q)).inv ≫
    presentedPerfectDGBFSOASpectrumComparison R (Q)

/-- 概要：同じ実 Perf 評価と SOA 比較からの実標的比較は全整数 π 同型。
方針：元の完全同値の逆と元の SOA 比較の全整数同型を使う。
規約：入力射の全自然性をこの対象別比較から結論しない。
使われ方：完備化前の実商の K 比較の標的照合。 -/
theorem dgKappaSuspensionNativePerfectToFixed_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKappaSuspensionNativePerfectToFixed R D I) :=
  (kSpectrumMap_piIsomorphism_of_equivalence
    (presentedPerfectDGBFEvaluationEquivalence R (Q)).symm).comp
    (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism R (Q))

/-- 概要：完備化前の同じ実商の native K から、同じ固定 K の実懸垂値への比較射。
方針：元の dg Yoneda K 射と同じ実標的比較を合成する。
規約：元の実商と固定 K の頂点を保持する。
使われ方：完備化前の fibration の loop 標的を元の反復列へ戻す。 -/
def dgKappaRawSuspensionToFixedK :
    kOmegaSpectrum (stableCategoryModel (dgKappaNativeSuspensionCategory R D I)) ⟶
      dgKInputSpectrum R (Q) :=
  kSpectrumMap (dgKappaRawSuspensionYonedaStableMap R D I) ≫
    dgKappaSuspensionNativePerfectToFixed R D I

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

set_option maxHeartbeats 800000 in
-- 同じ実商の native Yoneda と実 BF 標的比較の依存型を照合する。
include hcofinal in
/-- 概要：共終性供給に条件付きで、同じ実商から固定 K への実比較は全正次数 π 同型。
方針：元の Yoneda の共終性と同じ標的比較の全整数 π 同型を合成する。
規約：零次全射性や固定 ν の完備化後の Verdier 認証は要求しない。
使われ方：K-7 c5・d3 の一回 loop 後の非負次数比較。 -/
theorem dgKappaRawSuspensionToFixedK_positive (j : ℤ) (hj : 0 < j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaRawSuspensionToFixedK R D I) j) := by
  rw [dgKappaRawSuspensionToFixedK, OmegaSpectrum.homotopyMap_comp]
  change Function.Bijective ((OmegaSpectrum.homotopyMap
    (dgKappaSuspensionNativePerfectToFixed R D I) j) ∘
    (OmegaSpectrum.homotopyMap (kSpectrumMap (dgKappaRawSuspensionYonedaStableMap R D I)) j))
  exact Function.Bijective.comp (f := OmegaSpectrum.homotopyMap
    (kSpectrumMap (dgKappaRawSuspensionYonedaStableMap R D I)) j)
    (g := OmegaSpectrum.homotopyMap (dgKappaSuspensionNativePerfectToFixed R D I) j)
    (dgKappaSuspensionNativePerfectToFixed_piIsomorphism R D I j)
    ((hcofinal _ _ (dgKappaRawSuspensionYonedaStableMap R D I)
      (dgKappaRawSuspensionYoneda_isIdempotentCompletion R D I)).1 j hj)

set_option maxHeartbeats 800000 in
-- 同じ元の実商・実 Perf・固定 BF 値の零次比較の依存型を照合する。
include hcofinal in
/-- 概要：共終性供給に条件付きで、同じ実商から固定 K への比較は零次単射。
方針：元の Yoneda の零次単射と元の標的比較の単射を合成する。
規約：固定 K への零次全射性は要求しない。
使われ方：元の実 cone に対する完備化前後の比較条件。 -/
theorem dgKappaRawSuspensionToFixedK_zero_injective :
    Function.Injective (OmegaSpectrum.homotopyMap (dgKappaRawSuspensionToFixedK R D I) 0) := by
  have hbridge := dgKappaSuspensionNativePerfectToFixed_piIsomorphism R D I
  have hb := hbridge (0 : ℤ)
  have hy := (hcofinal _ _ (dgKappaRawSuspensionYonedaStableMap R D I)
    (dgKappaRawSuspensionYoneda_isIdempotentCompletion R D I)).2
  rw [dgKappaRawSuspensionToFixedK, OmegaSpectrum.homotopyMap_comp]
  intro x y hxy
  apply hy
  apply hb.1
  exact hxy

/-- 概要：完備化前の同じ実商から固定 K への実比較辺を、一回 native loop に送る。
方針：同じ実 BF 比較の元の一単体を Sp 正本の自己関手へ写す。
規約：同じ実商・固定 K の頂点を保持する。
使われ方：完備化前の fibration の loop 標的を元の構造射へ戻す。 -/
def dgKappaRawSuspensionToFixedLoopEdge :
    Sp.{max (u + 1) v}.Edge
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
          (stableCategoryModel (dgKappaNativeSuspensionCategory R D I)))))
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (Q)))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaRawSuspensionToFixedK R D I)).map
    OmegaSpectrum.nativeLoop.{max (u + 1) v}

set_option maxHeartbeats 800000 in
-- 同じ実商から固定 BF K への実比較を Sp の次数移動の自然性へ厳密に代入する。
include hcofinal in
/-- 概要：共終性供給に条件付きで、同じ実商から固定 K への一回 loop 比較は非負次数 π 同型。
方針：Sp 正本の自然な次数移動を同じ実比較辺に適用する。
規約：全単体写像の入力自然性や零次全射性は要求しない。
使われ方：K-7 c5・d3 の採用経路の標的比較。 -/
theorem dgKappaRawSuspensionToFixedLoopEdge_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaRawSuspensionToFixedLoopEdge R D I).toTruncated) j) := by
  have h := NatIso.isIso_map_iff (SpectrumHo.nativeLoopPiIso.{max (u + 1) v} j)
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaRawSuspensionToFixedK R D I)).toTruncated)
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective] at h
  apply h.mpr
  change Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaRawSuspensionToFixedK R D I)).toTruncated) (j + 1))
  rw [SpectrumHo.piMap_edge]
  change Function.Bijective (OmegaSpectrum.homotopyMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaRawSuspensionToFixedK R D I))) (j + 1))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge]
  exact dgKappaRawSuspensionToFixedK_positive R D I hcofinal (j + 1) (by omega)

end SerrePositivity.KST.NonConnective
