module

public import SerrePositivity.KST.DerivedBlowup.ExteriorGrading
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
概要：KST Def3.1 の Koszul 外積模型を実際の整数次数の複体にする。
方針：第n外積と収縮微分から自然数次数の chain complex を作り、n↦−n で延長する。
規約：基底環と生成加群は任意。有限性は後の反復 cone との比較で使用する。
使われ方：チャートの cdga の underlying complex と遷移射の構成。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- 概要：収縮微分から作る自然数次数の外積 Koszul 複体。
方針：ChainComplex.of に次数別収縮と平方零の証明を渡す。
規約：KST Def3.1、第n外積を homological 次数nに置く。
使われ方：整数 cochain 規約の複体への再添字。 -/
def exteriorKoszulChain (d : M →ₗ[R] R) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (ExteriorAlgebra.exteriorPower R n M))
    (fun n => ModuleCat.ofHom (exteriorDegreeDifferential d n)) (fun n => by
      ext z
      exact congrArg Subtype.val (exteriorDegreeDifferential_sq d n z))

/-- 概要：外積 Koszul 複体の整数次数版。
方針：自然数 chain 複体を n↦−n の複体形埋め込みで零延長する。
規約：KST Def3.1、cochain 次数−nに第n外積。
使われ方：既存 derivedChartComplex との比較と dg 代数への装備。 -/
def exteriorKoszulCochain (d : M →ₗ[R] R) : CochainComplex (ModuleCat.{max u v} R) ℤ :=
  (exteriorKoszulChain d).extend (ComplexShape.embeddingUpIntLE 0)

/-- 概要：整数次数−nの項は第n外積と同型。
方針：零延長の像の上での標準同型を使う。
規約：KST Def3.1。使われ方：次数ごとの積と反復 cone 比較の定義域。 -/
def exteriorKoszulCochainXIso (d : M →ₗ[R] R) (n : ℕ) :
    (exteriorKoszulCochain d).X (-(n : ℤ)) ≅
      ModuleCat.of R (ExteriorAlgebra.exteriorPower R n M) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE 0) (by simp)

/-- 概要：外積 Koszul 複体は正の cochain 次数で零。
方針：n↦−n の像に正次数がないことを使う。
規約：KST Def3.1 の connective 性、正則性は不要。
使われ方：dg 代数の非正次数条件。 -/
theorem exteriorKoszulCochain_isZero_X_pos (d : M →ₗ[R] R) (q : ℤ) (hq : 0 < q) :
    IsZero ((exteriorKoszulCochain d).X q) := by
  apply HomologicalComplex.isZero_extend_X
  intro n
  simp only [ComplexShape.embeddingUpIntLE_f, zero_sub]
  exact ne_of_lt (lt_of_le_of_lt (neg_nonpos.mpr (Int.natCast_nonneg n)) hq)

end SerrePositivity.KST.DerivedBlowup
