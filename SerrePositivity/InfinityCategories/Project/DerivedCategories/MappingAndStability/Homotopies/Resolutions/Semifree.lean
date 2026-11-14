module
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-! # 一点 dg 環から転送した semifree 複体 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree
open CategoryTheory MonoidalCategory
open DifferentialGraded
variable (S : Type u) [CommRing S]

/-- 概要：複体が一点 dg 環上の semifree 加群であるという対象の性質。
方針：評価同値の明示的な逆像 `ringModule` に filtration の存在を課す。
規約：係数環と加群は同じ宇宙に置く。使われ方：semifree dg 部分圏の対象条件。 -/
def complexSemifree : ObjectProperty (Complex S) := fun P =>
  moduleSemifree S PUnit.{1} (ForgetEnrichment.of (Complex S) (ringModule S P))

/-- 概要：semifree 条件は一点加群の filtration の存在そのものである。
方針：定義を展開する。規約：存在は `Nonempty`。使われ方：filtration の取り出し。 -/
theorem complexSemifree_iff (P : Complex S) : complexSemifree S P ↔
    Nonempty (ModuleSemifreeFiltration S PUnit.{1}
      (ForgetEnrichment.of (Complex S) (ringModule S P))) := Iff.rfl

/-- 概要：任意の一点加群の評価の semifree 性は元の加群の semifree 性と一致する。
方針：一点加群の復元等式で書き換える。規約：評価は唯一の対象で行う。
使われ方：semifree 解像度の転送。 -/
theorem complexSemifree_evaluation (M : ModuleCategory S PUnit.{1}) :
    complexSemifree S ((ringModuleEquivalence S).functor.obj M) ↔
      moduleSemifree S PUnit.{1} M := by
  change moduleSemifree S PUnit.{1}
    (ForgetEnrichment.of (Complex S)
      (ringModule S ((ForgetEnrichment.to (Complex S) M).obj (.op PUnit.unit)))) ↔ _
  rw [ringModule_recover]
  rfl

/-- 概要：一点加群の filtration の各段を通常の複体として読む。
方針：評価同値を各段に適用する。規約：段は自然数で添字付けする。
使われ方：複体上での filtration の展開。 -/
abbrev complexSemifreeStage {M : ModuleCategory S PUnit.{1}}
    (F : ModuleSemifreeFiltration S PUnit.{1} M) (n : ℕ) : Complex S :=
  (ringModuleEquivalence S).functor.obj (F.stage n)

/-- 概要：filtration の各商を通常の複体として読む。
方針：評価同値を商に適用する。規約：第 n 商は第 n+1 段の商。
使われ方：自由 sphere 表示を複体へ移す際の対象。 -/
abbrev complexSemifreeQuotient {M : ModuleCategory S PUnit.{1}}
    (F : ModuleSemifreeFiltration S PUnit.{1} M) (n : ℕ) : Complex S :=
  (ringModuleEquivalence S).functor.obj (F.quotient n)

/-- 概要：一点環上の自由 sphere の評価は通常の sphere と同型である。
方針：自由加群の評価は sphere と単位複体のテンソルなので右単位子を使う。
規約：sphere の次数は整数。使われ方：filtration の自由商の解釈。 -/
def freeSphereEvaluationIso (n : ℤ) :
    (ringModuleEquivalence S).functor.obj (freeSphere S PUnit.{1} PUnit.unit n) ≅
      complexSphere S n :=
  ρ_ (complexSphere S n)

set_option synthInstance.maxHeartbeats 40000 in
/-- 概要：自由 sphere 表示の評価は通常の sphere の余積と同型である。
方針：同値による余積の保存と各 sphere の右単位子を合成する。
規約：表示の添字集合をそのまま用いる。使われ方：初期段と各商の展開。 -/
def spherePresentationEvaluationIso {M : ModuleCategory S PUnit.{1}}
    (E : ModuleSphereFreePresentation S PUnit.{1} M) :
    (ringModuleEquivalence S).functor.obj M ≅
      ∐ (fun t : E.Index => complexSphere S (E.degree t)) := by
  letI := E.smallIndex
  refine (ringModuleEquivalence S).functor.mapIso E.iso ≪≫
    Limits.PreservesCoproduct.iso _ _ ≪≫ Limits.Sigma.mapIso (fun t => ?_)
  cases E.object t
  exact freeSphereEvaluationIso S (E.degree t)

/-- 概要：filtration の初期段は通常の sphere の余積である。
方針：初期段の自由表示を評価する。規約：初期段は第零段。
使われ方：semifree 条件の複体としての展開。 -/
def complexSemifreeStageZeroIso {M : ModuleCategory S PUnit.{1}}
    (F : ModuleSemifreeFiltration S PUnit.{1} M) :
    complexSemifreeStage S F 0 ≅
      ∐ (fun t : F.initial.Index => complexSphere S (F.initial.degree t)) :=
  spherePresentationEvaluationIso S F.initial

/-- 概要：filtration の各商は通常の sphere の余積である。
方針：商の自由表示を評価する。規約：次数は元の表示を継承する。
使われ方：semifree 商の複体としての展開。 -/
def complexSemifreeQuotientIso {M : ModuleCategory S PUnit.{1}}
    (F : ModuleSemifreeFiltration S PUnit.{1} M) (n : ℕ) :
    complexSemifreeQuotient S F n ≅
      ∐ (fun t : (F.quotientPresentation n).Index =>
        complexSphere S ((F.quotientPresentation n).degree t)) :=
  spherePresentationEvaluationIso S (F.quotientPresentation n)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree
