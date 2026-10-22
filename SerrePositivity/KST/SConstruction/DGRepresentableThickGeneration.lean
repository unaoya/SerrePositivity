module
public import SerrePositivity.KST.SConstruction.DGRepresentableFiniteCellThick
public import SerrePositivity.DifferentialGraded.Perfect.Enhancement

/-! # 指定代表一つの導来生成からホモトピー thick 生成へ
概要：同じ代表一つが Perf を生成すれば、射影的 perfect 加群はその thick 閉包に入る。
方針：既存の有限 cell retract 表示と射影的始域の導来 Hom 計算で retract を回収する。
規約：D の既存 Hom 計算を使う。使われ方：具体的商 End の再構成入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (b : D)
local notation "H" => moduleToHomotopy R D
local notation "Q" => moduleToDerived R D
local notation "L" => moduleHomotopyToDerivedClosed R D

/-- 同じ指定代表による導来 Perf 生成を、射影的加群のホモトピー thick 生成へ移す。 -/
lemma dgRepresentableThick_of_perfect
    (hgen : modulePerfectOver R D {b} = modulePerfect R D)
    (M : ModuleCategory R D) (hp : moduleHomotopicallyProjective R D M)
    (hM : modulePerfect R D ((Q).obj M)) :
    endomorphismThickClosure R D (representable R b) ((H).obj M) := by
  have hMb : modulePerfectOver R D {b} ((Q).obj M) := hgen ▸ hM
  obtain ⟨N, ⟨c⟩, ⟨r⟩⟩ := (modulePerfectOver_iff R D {b} ((Q).obj M)).mp hMb
  have hn : moduleHomotopicallyProjective R D N :=
    moduleFiniteCellOver_homotopicallyProjective R D ⟨c⟩
  let r' : Retract ((L).obj ((H).obj M)) ((L).obj ((H).obj N)) :=
    (Retract.ofIso ((moduleToHomotopyDerivedIso R D).app M)).trans
      (r.trans (Retract.ofIso ((moduleToHomotopyDerivedIso R D).app N).symm))
  obtain ⟨i, hi⟩ := (moduleProjectiveLocalization_map_bijective R D hp ((H).obj N)).2 r'.i
  obtain ⟨p, hq⟩ := (moduleProjectiveLocalization_map_bijective R D hn ((H).obj M)).2 r'.r
  let s : Retract ((H).obj M) ((H).obj N) :=
    ⟨i, p, by
      apply (moduleProjectiveLocalization_map_bijective R D hp ((H).obj M)).1
      rw [CategoryTheory.Functor.map_comp, hi, hq, r'.retract,
        CategoryTheory.Functor.map_id]⟩
  exact (endomorphismThickClosure R D (representable R b)).prop_of_retract s
    (dgRepresentableThick_of_finiteCell R D b c)

/-- 元の指定代表を、同じ全 Perf enhancement の実対象として保持する。 -/
def dgRepresentablePerfectPoint : PerfectDGModule R D :=
  ⟨representable R b, representable_homotopicallyProjective R D b,
    modulePerfectOver_representable R D b (Set.mem_univ _)⟩

/-- 同じ代表の導来単一生成は、既存 End 再構成定理の元の生成条件を満たす。 -/
lemma dgRepresentablePerfectPoint_thickGenerates
    (hgen : modulePerfectOver R D {b} = modulePerfect R D) :
    endomorphismThickGeneratesPerfect R D Set.univ (dgRepresentablePerfectPoint R D b) := by
  intro M
  exact dgRepresentableThick_of_perfect R D b hgen
    (ForgetEnrichment.of (Complex R) M.val) M.property.1 M.property.2

end SerrePositivity.KST.SConstruction
