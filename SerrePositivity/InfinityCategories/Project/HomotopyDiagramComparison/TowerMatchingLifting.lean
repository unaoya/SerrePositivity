module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TowerMaps
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FibrationTower
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence

/-!
概要：塔の射の初段と相対比較の持ち上げ性を実際の極限の射へ移す。
方針：次の標的成分と既存の源成分を引き戻しで同時指定して帰納的に持ち上げる。
規約：初段と各相対比較の右持ち上げ性を明示し、段ごとの持ち上げ性だけから推論しない。
使われ方：Goerss–Jardine I §§7–8、HTT A.3.3、Sp の塔の Ω 条件の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：相対比較の持ち上げ性は塔の全段で整合する持ち上げの族を与える。
方針：初段で充填し、次段の標的成分と前段の充填を引き戻しへまとめて反復する。
規約：任意の左射 j に対して、初段と全ての相対比較の持ち上げ性を要求する。
使われ方：塔の極限の比較射の RLP の対角射を構成する。 -/
lemma towerRelative_liftFamily {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    {T U : SSet.{u}} (j : T ⟶ U) [HasLiftingProperty j (f 0)]
    [∀ n, HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap f hf n)]
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X dX) (b : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit Y dY)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap f hf = j ≫ b) :
    ∃ l : ∀ n, U ⟶ X n,
      (∀ n, j ≫ l n = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X dX n) ∧
      (∀ n, l n ≫ f n = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection Y dY n) ∧
      (∀ n, l (n + 1) ≫ dX n = l n) := by
  have hs (n : ℕ) : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X dX n) ≫ f n =
      j ≫ (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection Y dY n) := by
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_projection f hf n, ← Category.assoc, h, Category.assoc]
  let LiftAt (n : ℕ) := {l : U ⟶ X n //
    j ≫ l = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X dX n ∧
      l ≫ f n = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection Y dY n}
  have h0 : Nonempty (LiftAt 0) := by
    let sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X dX 0) j (f 0)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection Y dY 0) := ⟨hs 0⟩
    exact ⟨⟨sq.lift, sq.fac_left, sq.fac_right⟩⟩
  have hn (n : ℕ) (prev : LiftAt n) :
      ∃ next : LiftAt (n + 1), next.val ≫ dX n = prev.val := by
    let v : U ⟶ pullback (dY n) (f n) :=
      pullback.lift (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection Y dY (n + 1)) prev.val (by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp, prev.property.2])
    let sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X dX (n + 1)) j
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap f hf n) v := ⟨by
      apply pullback.hom_ext
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap, pullback.lift_fst, v]
        exact hs (n + 1)
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap, pullback.lift_snd, v]
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp, prev.property.1]⟩
    have hb : sq.lift ≫ f (n + 1) = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection Y dY (n + 1) := by
      have he := congrArg (fun k : U ⟶ pullback (dY n) (f n) ↦
        k ≫ pullback.fst (dY n) (f n)) sq.fac_right
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap, pullback.lift_fst, v] using he
    have hd : sq.lift ≫ dX n = prev.val := by
      have he := congrArg (fun k : U ⟶ pullback (dY n) (f n) ↦
        k ≫ pullback.snd (dY n) (f n)) sq.fac_right
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap, pullback.lift_snd, v] using he
    exact ⟨⟨sq.lift, sq.fac_left, hb⟩, hd⟩
  let stage : ∀ n, LiftAt n := Nat.rec (Classical.choice h0) (fun n prev ↦ (hn n prev).choose)
  exact ⟨fun n ↦ (stage n).val, fun n ↦ (stage n).property.1,
    fun n ↦ (stage n).property.2, fun n ↦ (hn n (stage n)).choose_spec⟩

/-- 概要：初段と相対比較の右持ち上げ性は塔の極限の射へ移る。
方針：整合する持ち上げの族を既存の実際の極限の普遍性で束ねる。
規約：任意の左射 j の持ち上げ性を扱う。
使われ方：塔の fibration および全単射 RLP の比較。 -/
lemma towerMap_hasLiftingProperty {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    {T U : SSet.{u}} (j : T ⟶ U) [HasLiftingProperty j (f 0)]
    [∀ n, HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap f hf n)] :
    HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap f hf) := by
  constructor
  intro a b sq
  obtain ⟨l, ha, hb, hd⟩ := towerRelative_liftFamily f hf j a b sq.w
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift X dX l hd
  refine ⟨⟨{ l := v, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
    intro n
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection]
    exact ha n
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
    intro n
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap_projection, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection]
    exact hb n

/-- 概要：任意の射のクラスへの RLP は初段と相対比較から塔の極限の射へ移る。
方針：クラスの各射に対して整合する相対持ち上げを適用する。
規約：クラス W の閉性の仮定は不要。
使われ方：ホーン RLP と全ての単射への RLP の共通の判定。 -/
lemma towerMap_rlp {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (W : MorphismProperty SSet.{u})
    (h0 : W.rlp (f 0)) (hm : ∀ n, W.rlp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap f hf n)) : W.rlp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap f hf) := by
  intro T U j hj
  have : HasLiftingProperty j (f 0) := h0 j hj
  have (n : ℕ) : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap f hf n) := hm n j hj
  exact towerMap_hasLiftingProperty f hf j

/-- 概要：初段と全ての相対比較が Kan fibration なら塔の極限の射も Kan fibration。
方針：ホーンのクラスへの RLP の判定を適用する。
規約：各段の射の fibration 性だけを仮定する主張ではない。
使われ方：塔の比較の mapping path 因子分解の検証。 -/
lemma towerMap_fibration {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [Fibration (f 0)] [∀ n, Fibration (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap f hf n)] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap f hf) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  exact towerMap_rlp f hf J ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
    (fun n ↦ (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)

/-- 概要：初段と相対比較が全単射 RLP を持つ Kan な極限の射は全基点 π_* 同型。
方針：極限の射の全単射 RLP を構成して既存の実際の π_* 比較へ渡す。
規約：両極限の Kan 性を明示し、零次数も含む。
使われ方：Sp の塔の Ω 条件の比較の因子分解で使う判定。 -/
lemma towerMap_piIsomorphism_of_matching_rlp {X Y : ℕ → SSet.{u}}
    {dX : ∀ n, X (n + 1) ⟶ X n} {dY : ∀ n, Y (n + 1) ⟶ Y n}
    [KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X dX)] [KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit Y dY)]
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    (h0 : (MorphismProperty.monomorphisms SSet.{u}).rlp (f 0))
    (hm : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMatchingMap f hf n)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap f hf) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (towerMap_rlp f hf _ h0 hm)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
