module
public import SerrePositivity.KST.SConstruction.DGPerfectRealization
public import SerrePositivity.DifferentialGraded.Morita.PerfectProjectiveImage
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlyingInclusion
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence

/-!
概要：指定 perfect 値の実 tensor 評価を同じ実加群像のまま strict Perf に制限する。
方針：元代表評価同型と D 正本の perfect-projective 像保存を適用する。
規約：元全 Hom・実対象像を保持し、全 Perf の Small 性を要求しない。
使われ方：実二段 realization と固定 ν 値の全接続。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (J : DGFunctor R C (PerfectDGModule R E))

/-- 概要：実 tensor 評価の代表像は同じ指定 perfect 値と実同型で射影的 perfect。
方針：元の代表評価同型で指定値の証拠を運ぶ。
規約：元実加群を置換しない。使われ方：D の保存定理の生成元入力。 -/
lemma dgPerfectRealization_representable_perfectProjective (x : C) :
    modulePerfectProjectiveOver R E Set.univ
      ((dgPerfectRealization R C E J).obj (representable R x)) := by
  let e := dgPerfectRealizationRepresentableIso R C E J x
  exact ⟨moduleHomotopicallyProjective_of_iso R E e.symm (J.obj x).property.1,
    (modulePerfectOver R E Set.univ).prop_of_iso
      ((moduleToDerived R E).mapIso e.symm) (J.obj x).property.2⟩

/-- 概要：元実 tensor 評価は全射影的 perfect 加群を同じ性質の実加群へ送る。
方針：元代表像の実証拠を D 正本へ渡す。
規約：一般 dg 保存補題を再実装しない。使われ方：同じ実関手の strict Perf 制限。 -/
lemma dgPerfectRealization_perfectProjective {M : RightModule R C}
    (hM : modulePerfectProjectiveOver R C Set.univ M) :
    modulePerfectProjectiveOver R E Set.univ ((dgPerfectRealization R C E J).obj M) :=
  Morita.perfectDGFunctorImage_perfectProjective R C E (dgPerfectRealization R C E J)
    (dgPerfectRealization_representable_perfectProjective R C E J) hM

/-- 概要：同じ実 tensor 評価の全 Hom を持つ strict Perf 関手。
方針：元実関手を証明済みの性質保存で制限する。
規約：元対象像・全次数 Hom を保持。使われ方：元実二段評価の固定 ν 接続。 -/
def dgPerfectRealizationPerfect : DGFunctor R (PerfectDGModule R C) (PerfectDGModule R E) :=
  (dgPerfectRealization R C E J).restrict (modulePerfectProjectiveOver R C Set.univ)
    (modulePerfectProjectiveOver R E Set.univ)
    (fun _ hM => dgPerfectRealization_perfectProjective R C E J hM)

/-- 概要：同じ strict Perf 評価は全加群への包含後に元 tensor 評価を全回収する。
方針：元制限関手の包含則を適用する。
規約：全 dg 関手の等号。使われ方：元全実比較の端点を固定 ν へ照合する。 -/
lemma dgPerfectRealizationPerfect_inclusion :
    (dgPerfectRealizationPerfect R C E J).comp (perfectDGModuleInclusion R E Set.univ) =
      (perfectDGModuleInclusion R C Set.univ).comp (dgPerfectRealization R C E J) :=
  DGFunctor.restrict_comp_inclusion _ _ _ _

/-- 概要：元入力上の strict Perf 評価の全加群像は元の同じ実 tensor 後合成。
方針：同じ包含回収と厳密関手の結合則を使用する。
規約：元全 Hom・元実対象像を保持。使われ方：元実逆回転全比較の Perf 持ち上げ。 -/
lemma dgPerfectRealizationPerfect_underlying
    {P : Type z} [DGCategory R P] (F : DGFunctor R P (PerfectDGModule R C)) :
    dgPerfectModuleUnderlying R E (F.comp (dgPerfectRealizationPerfect R C E J)) =
      (dgPerfectModuleUnderlying R C F).comp (dgPerfectRealization R C E J) := by
  rw [dgPerfectModuleUnderlying_inclusion, strictDGFunctor_comp_assoc,
    dgPerfectRealizationPerfect_inclusion, ← strictDGFunctor_comp_assoc,
    ← dgPerfectModuleUnderlying_inclusion]
end SerrePositivity.KST.SConstruction

