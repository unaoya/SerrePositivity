module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedFiniteDiagonal
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteKanProductComparison
public import SerrePositivity.InfinityCategories.F1B.LeftFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.F1B.CofinalWeakEquivalence

/-!
概要：sifted な底上の元の有限非空 fiber 積の全空間 Kan 比較。
方針：元の全積射で元の有限対角を引き戻し、元の各射影の Kan 像を比較する。
規約：底の quasicategory 性は不要。元の全空間・射影・単位を保持する。
使われ方：P_Σ の sifted 余極限閉性に向けた、全有限積の元の全空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の有限非空族の全積射で元の対角を引き戻した、共通底の fiber 積。 -/
def finiteCommonFiberProduct (n : ℕ) {B : SSet.{u}} {E : Fin (n + 1) → SSet.{u}}
    (p : (i : Fin (n + 1)) → E i ⟶ B) : SSet.{u} :=
  pullback (nonemptyFiniteSSetProductMap n p) (nonemptyFiniteDiagonal B n)

/-- 元の共通 fiber 積から元の i 番目の全空間への射影。 -/
def finiteCommonFiberProductProjection (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (i : Fin (n + 1)) : finiteCommonFiberProduct n p ⟶ E i :=
  pullback.fst (nonemptyFiniteSSetProductMap n p) (nonemptyFiniteDiagonal B n) ≫
    nonemptyFiniteSSetProjection n E i

/-- 元の全射影は同じ元の底射影を被覆する。 -/
lemma finiteCommonFiberProductProjection_base (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (i : Fin (n + 1)) : finiteCommonFiberProductProjection n p i ≫ p i =
      pullback.snd (nonemptyFiniteSSetProductMap n p) (nonemptyFiniteDiagonal B n) := by
  rw [finiteCommonFiberProductProjection, Category.assoc,
    ← nonemptyFiniteSSetProductMap_projection, ← Category.assoc, pullback.condition,
    Category.assoc, nonemptyFiniteDiagonal_projection, Category.comp_id]

/-- sifted な共通底上の元の有限 fiber 積から元の全空間の反復積への射は right cofinal。 -/
lemma finiteCommonFiberProduct_isRightCofinal (n : ℕ) {B : SSet.{u}} [IsSiftedInfinity B]
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (hp : ∀ i, LeftFibration (p i)) : IsRightCofinal
      (pullback.fst (nonemptyFiniteSSetProductMap n p) (nonemptyFiniteDiagonal B n)) := by
  have : LeftFibration (nonemptyFiniteSSetProductMap n p) :=
    nonemptyFiniteSSetProductMap_leftFibration n p hp
  exact leftFibration_pullback_isRightCofinal _ _ (nonemptyFiniteDiagonal_isRightCofinal B n)

/-- 元の有限 fiber 積の Kan 模型から、元の全空間 Kan 模型の反復積への比較。 -/
def finiteCommonFiberProductKanComparison (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B) :
    F2.continuousKanReplacement.obj (finiteCommonFiberProduct n p) ⟶
      nonemptyFiniteSSetProduct n (fun i ↦ F2.continuousKanReplacement.obj (E i)) :=
  F2.continuousKanReplacement.map
    (pullback.fst (nonemptyFiniteSSetProductMap n p) (nonemptyFiniteDiagonal B n)) ≫
      continuousKanFiniteProductComparison n E

/-- 元の Kan 比較の全成分は、元の fiber 積射影の Kan 像そのもの。 -/
lemma finiteCommonFiberProductKanComparison_projection (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (i : Fin (n + 1)) : finiteCommonFiberProductKanComparison n p ≫
      nonemptyFiniteSSetProjection n (fun i ↦ F2.continuousKanReplacement.obj (E i)) i =
        F2.continuousKanReplacement.map (finiteCommonFiberProductProjection n p i) := by
  rw [finiteCommonFiberProductKanComparison, Category.assoc,
    continuousKanFiniteProductComparison_projection, ← Functor.map_comp]
  rfl

/-- 元の比較と元の全空間の Kan 単位の全成分は厳密に可換。 -/
lemma finiteCommonFiberProductKanComparison_unit (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B) :
    F2.continuousKanReplacementUnit.app (finiteCommonFiberProduct n p) ≫
      finiteCommonFiberProductKanComparison n p =
        pullback.fst (nonemptyFiniteSSetProductMap n p) (nonemptyFiniteDiagonal B n) ≫
          nonemptyFiniteSSetProductMap n (fun i ↦ F2.continuousKanReplacementUnit.app (E i)) := by
  rw [finiteCommonFiberProductKanComparison, ← Category.assoc,
    ← F2.continuousKanReplacementUnit.naturality, Functor.id_map,
    Category.assoc, continuousKanFiniteProductComparison_unit]

/-- sifted な共通底上の元の全有限非空 fiber 積の Kan 比較はホモトピー同値。 -/
lemma finiteCommonFiberProductKanComparison_homotopyEquivalence (n : ℕ)
    {B : SSet.{u}} [IsSiftedInfinity B] {E : Fin (n + 1) → SSet.{u}}
    (p : (i : Fin (n + 1)) → E i ⟶ B) (hp : ∀ i, LeftFibration (p i)) :
    IsSimplicialHomotopyEquivalence (finiteCommonFiberProductKanComparison n p) := by
  have : KanComplex (nonemptyFiniteSSetProduct n
      (fun i ↦ F2.continuousKanReplacement.obj (E i))) :=
    nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  have hf := F2.continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (finiteCommonFiberProduct_isRightCofinal n p hp).isWeakHomotopyEquivalence
  exact (hf.comp (continuousKanFiniteProductComparison_isWeakHomotopyEquivalence n E)
    ).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
