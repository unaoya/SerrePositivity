module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FibrationTower

/-!
概要：単体集合の逆向きの塔の射と相対比較の引き戻し。
方針：各段の可換な射の族を既存の整合族の極限へ持ち上げる。
規約：遷移は n+1 から n へ向かい、全ての可換条件は厳密な等式。
使われ方：Goerss–Jardine I §§7–8、HTT A.3.3、Sp の塔の Ω 条件の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：可換な各段の射が塔の実際の極限の間に誘導する射。
方針：各段の射影と与えられた射を合成し、整合族の普遍性へ渡す。
規約：Kan 性や fibration 性を仮定しない。
使われ方：塔の π_* 比較で検証する実際の射。 -/
def towerMap {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X dX ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit Y dY :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift Y dY (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X dX n ≫ f n) (by
    intro n
    rw [Category.assoc, ← hf n, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp])

/-- 概要：塔の極限の射を各段へ射影すると元の成分の射となる。
方針：整合族の極限への持ち上げの計算式を使う。
規約：任意の段 n についての射の等式。
使われ方：塔の可換正方形を各段の持ち上げ問題へ移す。 -/
lemma towerMap_projection {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (n : ℕ) :
    towerMap f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection Y dY n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X dX n ≫ f n := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection ..

/-- 概要：恒等射の族による塔の極限の射は恒等射。
方針：全ての段の射影の後で検査する。
規約：可換条件には圏の恒等射の法則を使う。
使われ方：塔の因子分解の合成の打ち消し。 -/
lemma towerMap_id (X : ℕ → SSet.{u}) (d : ∀ n, X (n + 1) ⟶ X n) :
    towerMap (fun n ↦ 𝟙 (X n)) (fun n ↦ by simp) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
  intro n
  rw [towerMap_projection, Category.comp_id, Category.id_comp]

/-- 概要：各段の射の合成は塔の極限の射の合成と一致する。
方針：全ての段の評価の後で二つの持ち上げを同定する。
規約：三つの塔の Kan 性は不要。
使われ方：mapping path による塔の比較の因子分解。 -/
lemma towerMap_comp {X Y Z : ℕ → SSet.{u}}
    {dX : ∀ n, X (n + 1) ⟶ X n} {dY : ∀ n, Y (n + 1) ⟶ Y n}
    {dZ : ∀ n, Z (n + 1) ⟶ Z n}
    (f : ∀ n, X n ⟶ Y n) (g : ∀ n, Y n ⟶ Z n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    (hg : ∀ n, dY n ≫ g n = g (n + 1) ≫ dZ n) :
    towerMap f hf ≫ towerMap g hg =
      towerMap (fun n ↦ f n ≫ g n) (fun n ↦ by
        rw [← Category.assoc, hf n, Category.assoc, hg n, ← Category.assoc]) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
  intro n
  rw [Category.assoc, towerMap_projection, ← Category.assoc,
    towerMap_projection, towerMap_projection, Category.assoc]

/-- 概要：塔の射の次段を標的の次成分と源の前成分の同時指定へ送る比較射。
方針：可換条件で二つの成分を引き戻しへ貼り合わせる。
規約：標的の遷移と前段の比較射の引き戻しを用いる。
使われ方：極限の射の相対持ち上げ性に必要な各段の比較。 -/
def towerMatchingMap {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (n : ℕ) :
    X (n + 1) ⟶ pullback (dY n) (f n) :=
  pullback.lift (f (n + 1)) (dX n) (hf n).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
