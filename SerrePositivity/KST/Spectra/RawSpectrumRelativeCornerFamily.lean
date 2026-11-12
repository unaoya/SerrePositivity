module

public import SerrePositivity.KST.Spectra.RawSpectrumRelativeCornerNext
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPrecomposition

/-!
概要：二変数 Raw Hom corner の持ち上げを全スペクトル段で構成する。
方針：零段の mapping corner 充填から相対 latching の充填を反復する。
規約：部分パラメータ・元の源・標的射影・構造可換性を同時に保持する。
使われ方：元の二変数 corner 写像の全単射 RLP の実証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 概要：相対 BF 源と標的射影を同時に固定した全段の整合した持ち上げ族。
方針：三つの境界式を持つ段を帰納構成し、相対 latching で構造可換性を保つ。
規約：各段の実射影が全単射 RLP を持つことだけを標的の条件とする。
使われ方：二変数 Raw Hom corner の実持ち上げ射。 -/
lemma relativeCornerFamily {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    (hi : IsSequentialRelativeCofibration i) {E Z : KanSequence.{u}}
    (q : KanSequence.Hom E Z)
    (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right)
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ space R E) (b : U ⟶ space R Z) (c : U ⟶ space X E)
    (hbc : b ≫ pre i Z = c ≫ post X q)
    (ha : a ≫ post R q = j ≫ b) (hc : a ≫ pre i E = j ≫ c) :
    ∃ l : ∀ n, U ⟶ (PointedObject.basedHom (R.level n).space (E.level n).space).right,
      (∀ n, j ≫ l n = a ≫ evaluation R E n) ∧
      (∀ n, l n ≫ (PointedObject.basedHomMap (R.level n).space (q.app n)).right =
        b ≫ evaluation R Z n) ∧
      (∀ n, l n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app n) (E.level n).space =
        c ≫ evaluation X E n) ∧
      (∀ n, l (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (R.sigma n) (E.level (n + 1)).space =
        l n ≫ step R E n) := by
  let LiftAt (n : ℕ) := {l : U ⟶
      (PointedObject.basedHom (R.level n).space (E.level n).space).right //
    j ≫ l = a ≫ evaluation R E n ∧
      l ≫ (PointedObject.basedHomMap (R.level n).space (q.app n)).right =
        b ≫ evaluation R Z n ∧
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app n) (E.level n).space = c ≫ evaluation X E n}
  have hbase (n : ℕ) : (b ≫ evaluation R Z n) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app n) (Z.level n).space =
    (c ≫ evaluation X E n) ≫
      (PointedObject.basedHomMap (X.level n).space (q.app n)).right := by
    rw [Category.assoc, ← pre_evaluation, ← Category.assoc, hbc,
      Category.assoc, post_evaluation, ← Category.assoc]
  have hboundary (n : ℕ) : (a ≫ evaluation R E n) ≫
      (PointedObject.basedHomMap (R.level n).space (q.app n)).right =
    j ≫ (b ≫ evaluation R Z n) := by
    rw [Category.assoc, ← post_evaluation, ← Category.assoc, ha, Category.assoc]
  have hsource (n : ℕ) : (a ≫ evaluation R E n) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app n) (E.level n).space = j ≫ (c ≫ evaluation X E n) := by
    rw [Category.assoc, ← pre_evaluation, ← Category.assoc, hc, Category.assoc]
  have hzero : Nonempty (LiftAt 0) := by
    let : Mono (i.app 0).right := hi.1
    obtain ⟨l, hl, hb, hs⟩ := PointedMapping.corner_family_lift
      (i.app 0) (q.app 0) (hq 0) j (a ≫ evaluation R E 0)
      (b ≫ evaluation R Z 0) (c ≫ evaluation X E 0)
      (hbase 0) (hboundary 0) (hsource 0)
    exact ⟨⟨l, hl, hb, hs⟩⟩
  have hnext (n : ℕ) (prev : LiftAt n) : ∃ next : LiftAt (n + 1),
      next.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (R.sigma n) (E.level (n + 1)).space =
        prev.val ≫ step R E n := by
    have huv : (prev.val ≫ step R E n) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ i.app n)
          (E.level (n + 1)).space =
      (c ≫ evaluation X E (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (E.level (n + 1)).space := by
      rw [Category.assoc, sequentialRawStep_pre, ← Category.assoc, prev.property.2.2,
        Category.assoc, ← evaluation_condition, ← Category.assoc]
    have hu : j ≫ (prev.val ≫ step R E n) =
      (a ≫ evaluation R E (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (R.sigma n) (E.level (n + 1)).space := by
      rw [← Category.assoc, prev.property.1, Category.assoc,
        ← evaluation_condition, ← Category.assoc]
    have hub : (prev.val ≫ step R E n) ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (R.level n).space) (q.app (n + 1))).right =
      (b ≫ evaluation R Z (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (R.sigma n) (Z.level (n + 1)).space := by
      have hstep := step_post R q n
      change step R E n ≫
          (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (R.level n).space) (q.app (n + 1))).right =
        (PointedObject.basedHomMap (R.level n).space (q.app n)).right ≫ step R Z n at hstep
      rw [Category.assoc, hstep, ← Category.assoc, prev.property.2.1,
        Category.assoc, ← evaluation_condition, ← Category.assoc]
    obtain ⟨l, hl, hb, hs, hf⟩ := relativeCornerNext i hi n (q.app (n + 1))
      (hq (n + 1)) j (a ≫ evaluation R E (n + 1)) (b ≫ evaluation R Z (n + 1))
      (c ≫ evaluation X E (n + 1)) (prev.val ≫ step R E n)
      huv hu (hsource (n + 1)).symm (hboundary (n + 1)) hub (hbase (n + 1)).symm
    exact ⟨⟨l, hl, hb, hf⟩, hs⟩
  let stage : ∀ n, LiftAt n := Nat.rec (Classical.choice hzero)
    (fun n prev ↦ (hnext n prev).choose)
  exact ⟨fun n ↦ (stage n).val, fun n ↦ (stage n).property.1,
    fun n ↦ (stage n).property.2.1, fun n ↦ (stage n).property.2.2,
    fun n ↦ (hnext n (stage n)).choose_spec⟩

end SerrePositivity.KST.Spectra.RawSpectrumMapping
