module
public import SerrePositivity.KST.SConstruction.DGOdotLandTamme
public import SerrePositivity.KST.SConstruction.DGKInputPerfectNu

/-!
概要：実 dg 入力の四完備性を証明して LT の Cat^perf 結論へ接続する。
方針：D から供給された証人を既存の同じ商・分裂・極限錐へ代入する。
規約：D2 f・具体的 β3・Sp-6 の未供給欄は除去しない。
使われ方：d の入力から追加の完備性仮定なしに得られる主定理の形式的部分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace DGOdotLaxVerdierInput
variable {R : Type u} [CommRing R] {d : DGOdotInput R}
  (h : DGOdotLaxVerdierInput R d)
  {F : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}} (hF : IsPerfectLocalizingInvariant F)

/-- 概要：四完備性を既証明の証人で満たす実 ⊙ の商入力。
方針：標準四証人を既存構成へ代入する。規約：同じ d の商射を保つ。
使われ方：具体的証拠の供給後も同じ LT 出力を使う入口。 -/
def perfectQuotient : PerfectLaxQuotient (dgOdotLowerExactMap R d)
    (dgOdotUpperExactMap R d) := (dgOdotCatPerfInput R d).perfectQuotient h

/-- 概要：d の入力だけを仮定する Cat^perf の LT 正方形。
方針：既存の四辺を固定する構成を特殊化する。
規約：追加の完備性仮定なし。使われ方：全 Cat^perf 局所化不変量での切除。 -/
def landTammeSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ Sp.{u + 1} :=
  (dgOdotCatPerfInput R d).landTammeSquare h hF

/-- 概要：同じ正方形を全局所化不変量が引き戻しへ送る。
方針：Tamme 分裂・実 Verdier 列・D の完備性を接続する。
規約：d の実証拠の存在は仮定のまま。使われ方：LT の Cat^perf 版の形式的結論。 -/
theorem landTamme_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (h.landTammeSquare hF) :=
  (dgOdotCatPerfInput R d).landTamme_isPullback h hF

/-- 概要：元の完備化後の二脚の実 cospan。
方針：同じ標準四証人で特殊化する。規約：脚を選び直さない。
使われ方：LT の極限錐の底。 -/
def landTammeCospan : (horn 2 2 : SSet.{u + 2}) ⟶ Sp.{u + 1} :=
  (dgOdotCatPerfInput R d).landTammeCospan h hF

/-- 概要：元の対角始域値を頂点とする同じ実錐。
方針：四証人を既存の錐へ代入する。規約：頂点を取り替えない。
使われ方：主定理の極限表示。 -/
def landTammeCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (h.landTammeCospan hF) :=
  (dgOdotCatPerfInput R d).landTammeCone h hF

/-- 概要：同じ二脚と頂点を持つ錐の ∞ 極限性。
方針：既存の極限証明へ D の証人を渡す。規約：群の比較だけで代用しない。
使われ方：d の仮定からの LT 極限結論。 -/
theorem landTammeCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (h.landTammeCone hF) :=
  (dgOdotCatPerfInput R d).landTammeCone_isLimit h hF

/-- 概要：極限錐の頂点は元の同じ ν 値への不変量値。
方針：固定 ν の Cat^perf 持ち上げの頂点式を使う。
規約：対象同値で弱めない。使われ方：固定 S での元の dg 対角始域の回収。 -/
lemma landTammeCone_source : (h.landTammeCone hF).vertex =
    (dgKInputPerfectNu R ≫ F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)) := by
  change (h.landTammeCone hF).vertex = F.app (Opposite.op ⦋0⦌)
    ((dgKInputPerfectNu R).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)))
  rw [dgKInputPerfectNu_vertex]
  exact (dgOdotCatPerfInput R d).landTammeCone_source h hF

end DGOdotLaxVerdierInput
end SerrePositivity.KST.SConstruction
