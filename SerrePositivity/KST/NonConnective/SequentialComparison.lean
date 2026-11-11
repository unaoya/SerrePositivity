module

public import SerrePositivity.KST.NonConnective.SequentialPi
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：逐次 BF 候補への比較の安定範囲と Sp の同値検出。
方針：整数 π 上の段での安定化から全単射性を得て、Sp の既存検出定理を適用する。
規約：dg 懸垂に対する安定化はまだ入力。連結 K との比較定理を完成扱いしない。
使われ方：K-7 の工程 4 への接続点。
-/

@[expose] public section

universe u

open CategoryTheory
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra

namespace SerrePositivity.KST.NonConnective

noncomputable section

/-- 概要：指定次数域での段の安定化は、同じ域で BF 候補への比較を全単射にする。
方針：次数ごとに群余極限の比較を適用する。
規約：域 P は全整数上の任意の述語であり、非負次数にも特殊化できる。
使われ方：後続の連結 K 比較の次数域の管理。 -/
theorem sequentialInjection_bijective_on (D : SpectrumSequence.{u}) (N : ℕ)
    (P : ℤ → Prop) (h : ∀ j, P j → ∀ (m : ℕ) (hm : N ≤ m),
      Function.Bijective (OmegaSpectrum.homotopyMap (D.map (homOfLE hm)) j)) :
    ∀ j, P j → Function.Bijective
      (OmegaSpectrum.homotopyMap (sequentialInjection D N) j) :=
  fun j hj ↦ sequentialInjection_bijective_of_stable D j N (h j hj)

local instance sequentialComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 概要：全整数次数で指定段から安定化している列では、同じ段の注入は Sp の可逆辺。
方針：群余極限の全単射性を整数 π による同値検出へ渡す。
規約：候補の ∞ 余極限性や Sp の IsStable は使わない。
使われ方：定数列・比較用列での BF 模型の検証。 -/
theorem sequentialInjection_isInvertible_of_stable (D : SpectrumSequence.{u}) (N : ℕ)
    (h : ∀ (j : ℤ) (m : ℕ) (hm : N ≤ m),
      Function.Bijective (OmegaSpectrum.homotopyMap (D.map (homOfLE hm)) j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialInjection D N)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (fun j ↦ sequentialInjection_bijective_of_stable D j N (h j))

end

end SerrePositivity.KST.NonConnective
