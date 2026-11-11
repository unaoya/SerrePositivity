module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionYonedaCompletion
public import SerrePositivity.KST.SConstruction.KSpectrumMaps
public import SerrePositivity.KST.SConstruction.PerfectDGStableModel
public import SerrePositivity.KST.LocalizingInvariants.SpectrumNativeLoopPi
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
概要：同じ実懸垂の Yoneda 完備化へ、K-S• の共終性供給境界を適用する。
方針：元の native 始域と実 Perf 値を安定模型に束ね、同じ Yoneda の実 K 射を使う。
規約：共終性命題を明示仮定引数に取る。完備化の同値性や K₀ 全射性は要求しない。
使われ方：K-6 c5 の実商と完備化の分離、K-7 c5・d3 の非負次数の loop 比較。
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
local instance suspensionCofinalitySpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "Q" => dgKappaSuspensionKInput R D I

/-- 概要：元の実懸垂の Yoneda 始域を、同じ native nerve の安定模型に保持する。
方針：D 正本の対象宇宙移送後の安定性へ同じ実商の前三角性を代入する。
規約：実商と元の対象ラベルを保持する。
使われ方：共終性の安定模型上の型への実代入。 -/
def dgKappaSuspensionYonedaSource : StableModel.{max (u + 1) v} where
  carrier := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (Q))
  stable := by
    let := dgKappaSuspension_isDGPretriangulated R D I
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftNerve_isStable R (Q)

/-- 概要：同じ実商からその実 Perf への元の Yoneda を、完全な同じ安定模型射とする。
方針：D 正本の同じ全 Hom 作用の完全性を S• 保存条件に渡す。
規約：固定 ν の認証や新しい関手を選ばない。
使われ方：K-S• の共終性で使う元の実 K 比較射の始点。 -/
def dgKappaSuspensionYonedaStableMap : dgKappaSuspensionYonedaSource R D I ⟶
    perfectDGStableModel R (Q) Set.univ := by
  let := dgKappaSuspension_isDGPretriangulated R D I
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isExactFunctor R (Q)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (Q), preservesCofiberData_of_isExactFunctor _⟩

/-- 概要：同じ実商の元の Yoneda が与える、完備化前後の実 BF K 射。
方針：K-S• の元の S• スペクトル射を同じ完全関手に適用する。
規約：固定 K と別の定義を選ばず、その native 模型間の実比較だけを構成する。
使われ方：完備化前の fibration と元の Perf 値を接続する。 -/
def dgKappaSuspensionYonedaKMap :
    kOmegaSpectrum (dgKappaSuspensionYonedaSource R D I) ⟶
      kOmegaSpectrum (perfectDGStableModel R (Q) Set.univ) :=
  kSpectrumMap (dgKappaSuspensionYonedaStableMap R D I)

/-- 概要：同じ完備化 K 比較の元の全一単体を一回 native loop へ写す。
方針：Sp 正本の同じ単体的自己関手を元の実辺へ適用する。
規約：BF 射や対象を点ごとに選び直さない。
使われ方：正次数の共終性を非負次数の構造比較へ移す。 -/
def dgKappaSuspensionYonedaLoopEdge :
    Sp.{max (u + 1) v}.Edge
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (dgKappaSuspensionYonedaSource R D I))))
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (perfectDGStableModel R (Q) Set.univ)))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionYonedaKMap R D I)).map
    OmegaSpectrum.nativeLoop.{max (u + 1) v}

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

include hcofinal in
/-- 概要：共終性供給に条件付きで、元の実懸垂の Yoneda K 射は全正整数次数で π 同型。
方針：同じ実商の元の Yoneda 完備化の認証を仮定引数へ代入する。
規約：供給命題の証明や I の実例の存在は主張しない。
使われ方：K-7 c5・d3 の loop 後の非負次数比較。 -/
theorem dgKappaSuspensionYonedaKMap_positive (j : ℤ) (hj : 0 < j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaSuspensionYonedaKMap R D I) j) :=
  (hcofinal _ _ (dgKappaSuspensionYonedaStableMap R D I)
    (dgKappaSuspensionYoneda_isIdempotentCompletion R D I)).1 j hj

include hcofinal in
/-- 概要：共終性供給に条件付きで、同じ元の Yoneda K 射は零次で単射。
方針：同じ実完備化の認証を仮定引数の零次結論へ代入する。
規約：零次全射性や商の冪等完備性は加えない。
使われ方：同じ cone の既存の K 零性を完備化前へ戻す。 -/
theorem dgKappaSuspensionYonedaKMap_zero_injective :
    Function.Injective (OmegaSpectrum.homotopyMap (dgKappaSuspensionYonedaKMap R D I) 0) :=
  (hcofinal _ _ (dgKappaSuspensionYonedaStableMap R D I)
    (dgKappaSuspensionYoneda_isIdempotentCompletion R D I)).2

include hcofinal in
/-- 概要：共終性供給に条件付きで、元の完備化比較の一回 loop は全非負次数で π 同型。
方針：Sp 正本の自然な loop 次数移動を同じ元の K 比較辺へ適用する。
規約：元の全一単体を保持し、一般 loop API を K-B に追加しない。
使われ方：K-7 c5・d3 の完備化前の連結 fibration からの接続。 -/
theorem dgKappaSuspensionYonedaLoopEdge_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaSuspensionYonedaLoopEdge R D I).toTruncated) j) := by
  have h := NatIso.isIso_map_iff (SpectrumHo.nativeLoopPiIso.{max (u + 1) v} j)
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionYonedaKMap R D I)).toTruncated)
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective] at h
  apply h.mpr
  change Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionYonedaKMap R D I)).toTruncated) (j + 1))
  rw [SpectrumHo.piMap_edge]
  change Function.Bijective (OmegaSpectrum.homotopyMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionYonedaKMap R D I))) (j + 1))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge]
  exact dgKappaSuspensionYonedaKMap_positive R D I hcofinal (j + 1) (by omega)

end SerrePositivity.KST.NonConnective
