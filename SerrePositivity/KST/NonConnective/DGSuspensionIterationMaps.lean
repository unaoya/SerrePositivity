module
public import SerrePositivity.KST.NonConnective.DGSuspensionIteration
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKMapLaws

/-!
概要：同じ段別 I・P と明示した増大可換射作用に沿う、反復懸垂の実入力射。
方針：各段で元の商射を使い、恒等・合成の整合性を再帰的に伝える。
規約：利用側は明示射作用とその厳密関手則に条件付き。その存在を主張しない。
使われ方：K-7 c4 の各反復段で同じ dg 入力射と固定 K の実 BF 射を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)
  (act : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R}, (A ⟶ B) →
    DGKappaSuspensionMapData R A B (s A).cone (s B).cone)

/-- 明示した同じ増大可換射作用に条件付きの、各反復段の実 dg 入力射。 -/
def dgSuspensionIterationMap {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    ∀ n, dgSuspensionIteration R s A n ⟶ dgSuspensionIteration R s B n
  | 0 => f
  | n + 1 => dgKappaSuspensionInputMap R _ _ _ _ (act (dgSuspensionIterationMap f n))

/-- 明示作用に条件付きで、初期段の全射は元の入力射そのもの。 -/
theorem dgSuspensionIterationMap_zero {A B : PerfDGInput.{u, max (u + 1) v} R}
    (f : A ⟶ B) : dgSuspensionIterationMap R s act f 0 = f := rfl

/-- 明示作用に条件付きで、次段も同じ平坦商からの射そのもの。 -/
theorem dgSuspensionIterationMap_succ {A B : PerfDGInput.{u, max (u + 1) v} R}
    (f : A ⟶ B) (n : ℕ) :
    dgSuspensionIterationMap R s act f (n + 1) = dgKappaSuspensionInputMap R _ _ _ _
      (act (dgSuspensionIterationMap R s act f n)) := rfl

variable
  (act_id : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    act (𝟙 A) = DGKappaSuspensionMapData.id R A (s A).cone)
  (act_comp : ∀ {A B C : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (g : B ⟶ C),
    act (f ≫ g) = DGKappaSuspensionMapData.comp R A B (s A).cone (s B).cone (act f) (act g))

include act_id in
/-- 明示射作用の恒等則に条件付きで、全反復段の入力射は厳密に恒等を保つ。 -/
theorem dgSuspensionIterationMap_id (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    dgSuspensionIterationMap R s act (𝟙 A) n = 𝟙 (dgSuspensionIteration R s A n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dgSuspensionIterationMap_succ, ih, act_id, dgKappaSuspensionInputMap_id]
    rfl

include act_comp in
/-- 明示射作用の合成則に条件付きで、全反復段の入力射は厳密に合成を保つ。 -/
theorem dgSuspensionIterationMap_comp {A B C : PerfDGInput.{u, max (u + 1) v} R}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    dgSuspensionIterationMap R s act (f ≫ g) n =
      dgSuspensionIterationMap R s act f n ≫ dgSuspensionIterationMap R s act g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dgSuspensionIterationMap_succ, ih, act_comp, dgKappaSuspensionInputMap_comp]
    rfl

/-- 明示作用と恒等・合成則に条件付きの、同じ n 回懸垂の厳密入力関手。 -/
def dgSuspensionIterationFunctor (n : ℕ) :
    PerfDGInput.{u, max (u + 1) v} R ⥤ PerfDGInput.{u, max (u + 1) v} R where
  obj A := dgSuspensionIteration R s A n
  map f := dgSuspensionIterationMap R s act f n
  map_id A := dgSuspensionIterationMap_id R s act act_id A n
  map_comp f g := dgSuspensionIterationMap_comp R s act act_comp f g n

/-- 明示作用に条件付きで、各反復段の元の厳密入力射を固定 K の実 BF 射へ送る。 -/
def dgSuspensionIterationSpectrumMap {A B : PerfDGInput.{u, max (u + 1) v} R}
    (f : A ⟶ B) (n : ℕ) :
    dgKInputSpectrum R (dgSuspensionIteration R s A n) ⟶
      dgKInputSpectrum R (dgSuspensionIteration R s B n) :=
  dgKInputSpectrumMap R (dgSuspensionIterationMap R s act f n)

include act_id in
/-- 明示恒等則に条件付きで、同じ全反復段の固定 K の実射は厳密に恒等を保つ。 -/
theorem dgSuspensionIterationSpectrumMap_id
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    dgSuspensionIterationSpectrumMap R s act (𝟙 A) n =
      𝟙 (dgKInputSpectrum R (dgSuspensionIteration R s A n)) := by
  unfold dgSuspensionIterationSpectrumMap
  rw [dgSuspensionIterationMap_id R s act act_id]
  exact presentedPerfectDGBFMap_id R _

include act_comp in
/-- 明示合成則に条件付きで、同じ全反復段の固定 K の実射は厳密に合成を保つ。 -/
theorem dgSuspensionIterationSpectrumMap_comp
    {A B C : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    dgSuspensionIterationSpectrumMap R s act (f ≫ g) n =
      dgSuspensionIterationSpectrumMap R s act f n ≫
        dgSuspensionIterationSpectrumMap R s act g n := by
  unfold dgSuspensionIterationSpectrumMap
  rw [dgSuspensionIterationMap_comp R s act act_comp]
  exact presentedPerfectDGBFMap_comp R _ _

end SerrePositivity.KST.NonConnective
