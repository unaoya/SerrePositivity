module
public import SerrePositivity.KST.SConstruction.DGFullClosedMapLift

/-!
概要：実加群に値を持つ全 dg 関手と閉比較を、同じ対象を持つ perfect 加群圏へ制限する。
方針：各実対象の射影的 perfect 証拠を付け、元全 Hom と元閉射を保持する。
規約：始域の dg 圏や対象を変更しない。使われ方：cell source 上の実比較を Perf 関手へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type w} [DGCategory R P]

/-- 概要：元実加群関手を同じ始域から同じ実 perfect 対象への dg 関手にする。
方針：元対象へ所属証拠を付け、全 Hom と単位・合成を継承する。
規約：始域と対象は不変。使われ方：実 graph 解像度の右制限を Perf に入れる。 -/
def dgPerfectModuleFunctorLift (F : DGFunctor R P (RightModule R E))
    (h : ∀ x, modulePerfectProjectiveOver R E Set.univ (F.obj x)) :
    DGFunctor R P (PerfectDGModule R E) where
  obj x := ⟨F.obj x, h x⟩
  map x y := F.map x y
  map_id x := F.map_id x
  map_comp x y z := F.map_comp x y z

/-- 概要：元の全 Hom 写像は同じ perfect 制限でも不変。
方針：元の定義を回収する。規約：全次数を保持。
使われ方：閉比較の全 Hom 自然性の輸送。 -/
lemma dgPerfectModuleFunctorLift_map (F : DGFunctor R P (RightModule R E))
    (h : ∀ x, modulePerfectProjectiveOver R E Set.univ (F.obj x)) (x y : P) :
    (dgPerfectModuleFunctorLift R E F h).map x y = F.map x y := rfl

/-- 概要：同じ制限関手を含めると元実加群関手を全 Hom で厳密回収する。
方針：元の対象と全 Hom を抽象関手として比較する。
規約：元関手を展開しない。使われ方：元 graph と実 Perf 関手の照合。 -/
lemma dgPerfectModuleFunctorLift_inclusion (F : DGFunctor R P (RightModule R E))
    (h : ∀ x, modulePerfectProjectiveOver R E Set.univ (F.obj x)) :
    (dgPerfectModuleFunctorLift R E F h).comp (perfectDGModuleInclusion R E Set.univ) = F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change F.map x y ≫ 𝟙 _ = F.map x y
  exact Category.comp_id _

variable (F G : DGFunctor R P (RightModule R E))
  (hF : ∀ x, modulePerfectProjectiveOver R E Set.univ (F.obj x))
  (hG : ∀ x, modulePerfectProjectiveOver R E Set.univ (G.obj x))
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))

/-- 概要：同じ元閉比較射を同じ実 perfect 対象間へ持ち上げる。
方針：元閉射の充満部分圏への明示的持ち上げを使う。
規約：元射を保持。使われ方：実 graph 比較の Perf 表示。 -/
def dgPerfectModuleFunctorLiftComparisonMap (x : P) :
    ForgetEnrichment.of (Complex R) ((dgPerfectModuleFunctorLift R E F hF).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((dgPerfectModuleFunctorLift R E G hG).obj x) :=
  dgPerfectClosedMapLift R E ((dgPerfectModuleFunctorLift R E F hF).obj x)
    ((dgPerfectModuleFunctorLift R E G hG).obj x) (a x)

/-- 概要：元実加群の全 Hom 自然性は同じ perfect 制限へ移る。
方針：元の全 Hom 回収と閉射の前後合成回収を使う。
規約：元全次数を保持。使われ方：実比較を dg 自然変換へ束ねる。 -/
lemma dgPerfectModuleFunctorLiftComparisonMap_hom_naturality
    (h : ∀ x y, F.map x y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y))) (x y : P) :
    (dgPerfectModuleFunctorLift R E F hF).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgPerfectModuleFunctorLift R E F hF).obj x))
        (dgPerfectModuleFunctorLiftComparisonMap R E F G hF hG a y) =
    (dgPerfectModuleFunctorLift R E G hG).map x y ≫
      eHomWhiskerRight (Complex R) (dgPerfectModuleFunctorLiftComparisonMap R E F G hF hG a x)
        (ForgetEnrichment.of (Complex R) ((dgPerfectModuleFunctorLift R E G hG).obj y)) := by
  have hl := dgPerfectClosedMapLift_whiskerLeft R E
    ((dgPerfectModuleFunctorLift R E F hF).obj y) ((dgPerfectModuleFunctorLift R E G hG).obj y)
    ((dgPerfectModuleFunctorLift R E F hF).obj x) (a y)
  have hr := dgPerfectClosedMapLift_whiskerRight R E
    ((dgPerfectModuleFunctorLift R E F hF).obj x) ((dgPerfectModuleFunctorLift R E G hG).obj x)
    ((dgPerfectModuleFunctorLift R E G hG).obj y) (a x)
  exact (congrArg₂ (fun k l => k ≫ l) (dgPerfectModuleFunctorLift_map R E F hF x y) hl).trans
    ((h x y).trans (congrArg₂ (fun k l => k ≫ l)
      (dgPerfectModuleFunctorLift_map R E G hG x y) hr).symm)
end SerrePositivity.KST.SConstruction
