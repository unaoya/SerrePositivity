module
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlying
/-!
概要：元 Perf 関手の全加群表示と元の全包含後合成を照合する。
方針：同じ対象と Hom 作用上の恒等合成を回収する。
規約：元全関手の等号。使われ方：同じ実 Perf 延長の native 全比較への接続。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type w} [DGCategory R P] (F : DGFunctor R P (PerfectDGModule R E))
/-- 概要：元 Perf 関手の全加群表示は元の全包含との合成。
方針：元全 Hom の恒等後合成を消去する。
規約：元関手の等号。使われ方：実全比較の native 延長終端の照合。 -/
lemma dgPerfectModuleUnderlying_inclusion :
    dgPerfectModuleUnderlying R E F = F.comp (perfectDGModuleInclusion R E Set.univ) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := dgPerfectModuleUnderlying R E F)
    (G := F.comp (perfectDGModuleInclusion R E Set.univ)) (fun _ => rfl)
  intro x y
  change F.map x y ≫ 𝟙 _ = F.map x y ≫ 𝟙 _
  rfl
end SerrePositivity.KST.SConstruction
