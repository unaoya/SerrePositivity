module

public import SerrePositivity.InfinityCategories.F1.Limits.InverseSequenceReplacementCorners

/-!
概要：相対的な持ち上げを持つ可算の塔の、成分ごとの同値による極限の比較。
方針：自然な可逆 path 置換の両端の極限を全境界持ち上げにし、標準切断で比較を回収する。
規約：一般の厳密極限や持ち上げ条件のない塔に対する同値不変性は仮定しない。
使われ方：可算骨格の局所化比較を一般の底へ貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet Opposite
namespace SerrePositivity.InfinityCategories

/-- 可算の塔の初段と相対 corner の全境界持ち上げは、標準の極限比較にも移る。 -/
lemma trivialKanFibration_limMap_inverseSequence {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G)
    [TrivialKanFibration (η.app (op 0))]
    [∀ n, TrivialKanFibration (inverseSequenceCorner η n)] : TrivialKanFibration (limMap η) :=
  trivialKanFibration_inverseSequenceConeMap η _ _ (limit.isLimit F) (limit.isLimit G)
    (limMap η) (limMap_π η)

/-- 相対的な持ち上げを持つ可算の塔は、成分ごとの同値を極限の前合成同値へ移す。 -/
lemma isPrecompositionEquivalence_limMap_inverseSequence {F G : ℕᵒᵖ ⥤ SSet.{u}}
    [∀ j, Quasicategory (F.obj j)] [∀ j, Quasicategory (G.obj j)]
    (η : F ⟶ G) (hη : ∀ j, IsQCatEquivalence (η.app j))
    (hF : ∀ n, SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (F.map (homOfLE (Nat.le_succ n)).op))
    (hG : ∀ n, SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (G.map (homOfLE (Nat.le_succ n)).op))
    [∀ n, TrivialKanFibration
      (relativeEquivalencePathMapAt (G.map (homOfLE (Nat.le_succ n)).op) 0)] :
    IsPrecompositionEquivalence (limMap η) := by
  let R := inverseSequencePathDiagram η
  let p := inverseSequencePathProjection η
  let q := inverseSequencePathEndpoint η
  let s := inverseSequencePathSection η
  have : TrivialKanFibration (p.app (op 0)) := by
    change TrivialKanFibration (equivalencePathReplacementProjection (η.app (op 0)))
    infer_instance
  have : ∀ n, TrivialKanFibration (inverseSequenceCorner p n) :=
    fun n ↦ trivialKanFibration_inverseSequenceCorner_projection η n
  have hp : TrivialKanFibration (limMap p) := trivialKanFibration_limMap_inverseSequence p
  have : TrivialKanFibration (q.app (op 0)) :=
    (hη (op 0)).equivalencePathReplacementMap_trivialKanFibration
  have : ∀ n, TrivialKanFibration (inverseSequenceCorner q n) := fun n ↦
    trivialKanFibration_inverseSequenceCorner_endpoint η n (hη _) (hη _) (hF n) (hG n)
  have hq : TrivialKanFibration (limMap q) := trivialKanFibration_limMap_inverseSequence q
  have : ∀ n, InnerFibration (F.map (homOfLE (Nat.le_succ n)).op) := fun n ↦
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.innerFibration (hF n)
  have : ∀ n, InnerFibration (G.map (homOfLE (Nat.le_succ n)).op) := fun n ↦
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.innerFibration (hG n)
  have : Quasicategory (limit F) := quasicategory_of_inverseSequence_limit F _ (limit.isLimit F)
  have : Quasicategory (limit G) := quasicategory_of_inverseSequence_limit G _ (limit.isLimit G)
  have : Quasicategory (limit R) := quasicategory_of_innerFibration (limMap p)
  have hsp : limMap s ≫ limMap p = 𝟙 (limit F) := by
    change lim.map s ≫ lim.map p = 𝟙 _
    rw [← lim.map_comp, inverseSequencePathSection_projection, lim.map_id]
  have hsq : limMap s ≫ limMap q = limMap η := by
    change lim.map s ≫ lim.map q = lim.map η
    rw [← lim.map_comp, inverseSequencePathSection_endpoint]
  have hs : IsQCatEquivalence (limMap s) := by
    apply (isQCatEquivalence_of_trivialKanFibration (limMap p)).cancel_right
    rw [hsp]
    exact (QCatEquivalence.refl _).isQCatEquivalence
  have he : IsQCatEquivalence (limMap η) := by
    rw [← hsq]
    exact hs.comp (isQCatEquivalence_of_trivialKanFibration (limMap q))
  exact he.isPrecompositionEquivalence

/-- 可算の塔の任意の極限錐でも、相対持ち上げを持つ成分ごとの同値は同値を誘導する。 -/
lemma isPrecompositionEquivalence_inverseSequenceConeMap {F G : ℕᵒᵖ ⥤ SSet.{u}}
    [∀ j, Quasicategory (F.obj j)] [∀ j, Quasicategory (G.obj j)]
    (η : F ⟶ G) (hη : ∀ j, IsQCatEquivalence (η.app j))
    (hF : ∀ n, SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (F.map (homOfLE (Nat.le_succ n)).op))
    (hG : ∀ n, SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (G.map (homOfLE (Nat.le_succ n)).op))
    [∀ n, TrivialKanFibration
      (relativeEquivalencePathMapAt (G.map (homOfLE (Nat.le_succ n)).op) 0)]
    (c : Cone F) (d : Cone G) (hc : IsLimit c) (hd : IsLimit d) (φ : c.pt ⟶ d.pt)
    (hφ : ∀ j, φ ≫ d.π.app j = c.π.app j ≫ η.app j) : IsPrecompositionEquivalence φ := by
  let ec := hc.conePointUniqueUpToIso (limit.isLimit F)
  let ed := hd.conePointUniqueUpToIso (limit.isLimit G)
  have he : φ ≫ ed.hom = ec.hom ≫ limMap η := by
    apply limit.hom_ext
    intro j
    dsimp only [ec, ed]
    rw [Category.assoc, limit.conePointUniqueUpToIso_hom_comp, Category.assoc,
      limMap_π, ← Category.assoc, limit.conePointUniqueUpToIso_hom_comp]
    exact hφ j
  apply (isPrecompositionEquivalence_of_iso ed).cancel_right
  rw [he]
  exact (isPrecompositionEquivalence_of_iso ec).comp
    (isPrecompositionEquivalence_limMap_inverseSequence η hη hF hG)

end SerrePositivity.InfinityCategories
