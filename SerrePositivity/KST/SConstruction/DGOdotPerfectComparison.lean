module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.DGOdotAlgebraRealization
public import SerrePositivity.KST.SConstruction.DGOdotGeneratorConditions
public import SerrePositivity.DifferentialGraded.Verdier.Derived
public import SerrePositivity.DifferentialGraded.Morita.Perfect

/-! # 実 ⊙ 代数から元の対角商への同じ Perf 延長
概要：代数の一対象圏から指定 End を通る元の商への実射を固定する。
方針：D の導来 graph 合成比較を主 Perf へ制限し、既存の二同値を移す。
規約：二つの実自由生成条件は明示入力。使われ方：元の ⊙ の Perf 商比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d)
local notation "I" => dgOdotQuotientInput R d
local notation "Q" => DGOdotQuotientEnd R d
local notation "T" => DGLaxQuotientEndInput.quotientObject (I)
local notation "F" => dgOdotAlgebraToEnd R d
local notation "G" => DGLaxQuotientEndInput.endInclusion (I)

/-- 実 ⊙ の右加群用圏から、同じ元の対角商への実 dg 射。 -/
def dgOdotAlgebraToQuotient : DGFunctor R (B) (T) := (F).comp (G)

/-- 二回の元の主 Perf 延長と、同じ合成射の一回延長の指定自然同型。 -/
def dgOdotAlgebraQuotientPerfectCompositionIso :
    quasiEquivalencePerfectExtension R (B) (Q) (F) ⋙
      quasiEquivalencePerfectExtension R (Q) (T) (G) ≅
        quasiEquivalencePerfectExtension R (B) (T) (dgOdotAlgebraToQuotient R d) :=
  Morita.perfectFunctorCompositionIso R (B) (Q) (T)
    (dgDerivedExtension R (B) (Q) (F)) (dgDerivedExtension R (Q) (T) (G))
    (fun _ h => dgDerivedExtension_perfect R (B) (Q) (F) h)
    (fun _ h => dgDerivedExtension_perfect R (Q) (T) (G) h) ≪≫
      Morita.perfectFunctorIso R (B) (T) _ _
        (fun _ h => dgDerivedExtension_perfect R (Q) (T) (G)
          (dgDerivedExtension_perfect R (B) (Q) (F) h))
        (fun _ h => dgDerivedExtension_perfect R (B) (T)
          (dgOdotAlgebraToQuotient R d) h)
        (derivedGraphExtensionCompositionIso R (B) (Q) (T) (F) (G))

/-- 同じ実自由生成条件の下で、元の ⊙ から商への射の主 Perf 延長自体が同値。 -/
lemma dgOdotAlgebraToQuotient_isMorita (hgen : DGOdotGeneratorConditions R d) :
    (quasiEquivalencePerfectExtension R (B) (T) (dgOdotAlgebraToQuotient R d)).IsEquivalence := by
  letI : (quasiEquivalencePerfectExtension R (B) (Q) (F)).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R (B) (Q) (F)
    (dgOdotAlgebraToEnd_quasiEquivalence R d)).isEquivalence_functor
  letI : (quasiEquivalencePerfectExtension R (Q) (T) (G)).IsEquivalence :=
    dgOdotEndInclusion_isMorita R d hgen
  exact Functor.isEquivalence_of_iso (dgOdotAlgebraQuotientPerfectCompositionIso R d)

/-- 順方向を元の一回延長に固定した、同じ実 ⊙ と元の商の Perf 同値。 -/
def dgOdotAlgebraQuotientPerfectEquivalence (hgen : DGOdotGeneratorConditions R d) :
    PerfectModuleCategory R (B) ≌ PerfectModuleCategory R (T) := by
  letI := dgOdotAlgebraToQuotient_isMorita R d hgen
  exact (quasiEquivalencePerfectExtension R (B) (T) (dgOdotAlgebraToQuotient R d)).asEquivalence

/-- 同じ元の ⊙ から商への射の実 dg Perf 延長も、二生成条件の下で準同値。 -/
lemma dgOdotAlgebraToQuotient_perfectDG_quasiEquivalence
    (hgen : DGOdotGeneratorConditions R d) :
    QuasiEquivalence (perfectDGExtension R (B) (T) (dgOdotAlgebraToQuotient R d)) := by
  letI := dgOdotAlgebraToQuotient_isMorita R d hgen
  exact perfectDGExtension_quasiEquivalence R (B) (T) (dgOdotAlgebraToQuotient R d)

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Eq (4)" (partial := component) "仮定：可換基礎環上の指定 dg gluing の Milnor 正方形、Sp 値かつ filtered 余極限保存の局所化不変量（Lean が強い）。結論：実 resolved 商の冪等完備化を第 4 頂点とする Sp 引き戻しと、dg End の Morita 比較。任意の E₁ 環スペクトルについての自然な環の四辺と下部スペクトル A′⊗_A B の同定は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotAlgebraToQuotient_isMorita
attribute [cite LT "Eq (9)" (partial := component) "仮定：左右の小 perfect 模型の生成条件と指定 dg gluing（Lean が強い）。結論：指定 End から dg 商への Morita 同値。任意の E₁ 正方形で p(τ) が同値との比較は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotAlgebraToQuotient_isMorita
attribute [cite LT "Lemma 1.10" (partial := component) "仮定：線形 dg 模型、生成条件または Morita の証人（Lean が強い）。結論：特定の生成元の End と perfect 商の比較、Morita からの ∞ 圏同値。E₁ 環スペクトル全体の充満忠実な関手と本質像は得ない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotAlgebraToQuotient_isMorita
attribute [cite LT "Lemma 1.11" (partial := component) "仮定：左右の小 perfect 模型の生成条件と指定 dg gluing（Lean が強い）。結論：指定 End から dg 商への Morita 同値。任意の E₁ 正方形で p(τ) が同値との比較は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotAlgebraToQuotient_isMorita
attribute [cite LT "Thm 1.3" (partial := component) "仮定：可換基礎環上の指定 dg gluing の Milnor 正方形、Sp 値かつ filtered 余極限保存の局所化不変量（Lean が強い）。結論：実 resolved 商の冪等完備化を第 4 頂点とする Sp 引き戻しと、dg End の Morita 比較。任意の E₁ 環スペクトルについての自然な環の四辺と下部スペクトル A′⊗_A B の同定は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotAlgebraToQuotient_isMorita
