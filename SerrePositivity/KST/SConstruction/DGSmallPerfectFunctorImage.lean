module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelope
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence

/-!
概要：小さい始域からの実 Perf 関手を、同じ全像を含む小模型へ厳密に因子化する。
方針：元の像対象族を同じ小さい Perf 包絡の指定族へ加え、全 Hom を保持する。
規約：全 Perf の Small 性や同型な代表の選択は使用しない。
使われ方：恒等 lax 差の実 cone 関手を固定 S の辺へ持ち込む。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C (PerfectDGModule R D))

/-- 概要：元の実 Perf 関手の全像対象を含む同じ小模型。
方針：元の対象像族を指定追加族にする。規約：全対象を小さいと仮定しない。
使われ方：実 cone 差の固定 S 終域。 -/
abbrev DGSmallPerfectFunctorImage := DGSmallPerfectEnvelope R D C F.obj

/-- 概要：同じ実 Perf 関手を元の全像を含む小模型へ持ち上げる厳密 dg 関手。
方針：対象は元の像そのもの、全 Hom は元の写像。
規約：対象別同型で共役しない。使われ方：固定 S の実 cone 差の辺。 -/
def dgSmallPerfectFunctorImageLift : DGFunctor R C (DGSmallPerfectFunctorImage R C D F) where
  obj x := dgSmallPerfectEnvelopeOfFamily R D C F.obj x
  map x y := F.map x y
  map_id x := F.map_id x
  map_comp x y z := F.map_comp x y z

omit [Small.{u} C] in
/-- 概要：同じ小模型を元の Perf へ含めると元の実関手を厳密に回収する。
方針：同じ対象像と全 Hom 上の恒等包含を使用する。
規約：全 dg 関手の等号。使われ方：元 cone 関手と ν 像の全比較。 -/
lemma dgSmallPerfectFunctorImageLift_inclusion :
    (dgSmallPerfectFunctorImageLift R C D F).comp
      (dgSmallPerfectEnvelopeInclusion R D C F.obj) = F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change F.map x y ≫ 𝟙 _ = _
  exact Category.comp_id _

end SerrePositivity.KST.SConstruction
