module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.TowerPiComparison
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：点つき単体集合の逆向きの塔の明示的極限と通常の極限錐。
方針：整合族の極限に基点の整合族を加え、既存の射影と持ち上げを点つきに束ねる。
規約：台は FibrationTower.limit そのもの。Kan 性や fibration 性は要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT 4.2.4.1、Sp の段ごとの塔の極限。
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

/-- 概要：点つき塔の極限。
方針：各段の基点射を整合族の極限へ持ち上げる。
規約：塔の向きは n+1 から n。
使われ方：スペクトルの極限の各段。 -/
def pointedTowerLimit (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) : PointedSimplicialSet.{u} :=
  Under.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift (fun n ↦ (X n).right) (fun n ↦ (d n).right)
    (fun n ↦ (X n).hom) (fun n ↦ Under.w (d n)))

/-- 概要：Kan な初段と fibration の遷移を持つ点つき塔の極限は Kan。
方針：基礎単体集合の整合族の極限の Kan 性を使う。
規約：全段の Kan 性を別々に要求せず、初段だけで十分。
使われ方：Sp の塔の各段と随伴比較の全基点 π_* 同型性。 -/
instance pointedTowerLimit_kanComplex (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n, Fibration (d n).right] [KanComplex (X 0).right] :
    KanComplex (pointedTowerLimit X d).right := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit_kanComplex _ _

/-- 概要：点つき塔の極限から各段への射影。
方針：整合族の評価を基点保存付きで束ねる。
規約：基礎射は既存の projection。
使われ方：極限の構造射と錐の脚。 -/
def pointedTowerProjection (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) (n : ℕ) : pointedTowerLimit X d ⟶ X n :=
  Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (d n).right) n)
    (by rfl)

/-- 概要：点つき極限の射影は隣接遷移と可換。
方針：基礎射の整合族の等式を使う。
規約：厳密な点つき射の等式。
使われ方：極限錐の自然性。 -/
lemma pointedTowerProjection_comp (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) (n : ℕ) :
    pointedTowerProjection X d (n + 1) ≫ d n = pointedTowerProjection X d n := by
  apply Under.UnderMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp (fun n ↦ (X n).right) (fun n ↦ (d n).right) n

/-- 概要：整合する点つき射の族を点つき塔の極限へ持ち上げる。
方針：基礎射を持ち上げ、全射影の後で基点保存を確認する。
規約：整合条件は各隣接段で要求する。
使われ方：極限の普遍性と構造射の構成。 -/
def pointedTowerLift {A : PointedSimplicialSet.{u}} (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) (f : ∀ n, A ⟶ X n)
    (hf : ∀ n, f (n + 1) ≫ d n = f n) : A ⟶ pointedTowerLimit X d :=
  Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift (fun n ↦ (X n).right) (fun n ↦ (d n).right)
    (fun n ↦ (f n).right) (fun n ↦ congrArg Under.Hom.right (hf n))) (by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
      intro n
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection, Under.w]
      rfl)

/-- 概要：点つきの持ち上げの各射影は指定した成分に等しい。
方針：基礎射の持ち上げの計算則を使う。
規約：整合性の証明の選択に依存しない。
使われ方：極限の構造射の成分計算。 -/
lemma pointedTowerLift_projection {A : PointedSimplicialSet.{u}}
    (X : ℕ → PointedSimplicialSet.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    (f : ∀ n, A ⟶ X n) (hf : ∀ n, f (n + 1) ≫ d n = f n) (n : ℕ) :
    pointedTowerLift X d f hf ≫ pointedTowerProjection X d n = f n := by
  apply Under.UnderMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection (fun n ↦ (X n).right) (fun n ↦ (d n).right)
    (fun n ↦ (f n).right) (fun n ↦ congrArg Under.Hom.right (hf n)) n

/-- 概要：点つき塔の極限への射は全射影で決まる。
方針：基礎射を整合族の外延性で比較する。
規約：始域は任意の点つき単体集合。
使われ方：極限の一意性と同型の検証。 -/
lemma pointedTowerLimit_hom_ext {A : PointedSimplicialSet.{u}}
    (X : ℕ → PointedSimplicialSet.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    {f g : A ⟶ pointedTowerLimit X d}
    (h : ∀ n, f ≫ pointedTowerProjection X d n = g ≫ pointedTowerProjection X d n) : f = g := by
  apply Under.UnderMorphism.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext
  intro n
  exact congrArg Under.Hom.right (h n)

/-- 概要：点つき塔の明示的極限を頂点とする通常の錐。
方針：隣接段の可換式から自然変換を作る。
規約：添字圏は ℕ の反対圏。
使われ方：loop の右随伴性による極限保存。 -/
def pointedTowerCone (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) : Cone (Functor.ofOpSequence d) where
  pt := pointedTowerLimit X d
  π := NatTrans.ofOpSequence (fun n ↦ pointedTowerProjection X d n) (fun n ↦ by
    change 𝟙 _ ≫ pointedTowerProjection X d n =
      pointedTowerProjection X d (n + 1) ≫ (Functor.ofOpSequence d).map _
    rw [Category.id_comp, Functor.ofOpSequence_map_homOfLE_succ]
    exact (pointedTowerProjection_comp X d n).symm)

/-- 概要：明示的な点つき塔の錐は通常の極限錐。
方針：任意の錐の各脚を持ち上げ、射影で普遍性を検証する。
規約：Kan 性や fibration 性を要求しない。
使われ方：Sp の塔の段ごとの極限と loop との比較。 -/
def pointedTowerCone_isLimit (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) : IsLimit (pointedTowerCone X d) where
  lift c := pointedTowerLift X d (fun n ↦ c.π.app (Opposite.op n)) (fun n ↦ by
    simpa only [Functor.ofOpSequence_map_homOfLE_succ] using
      c.w (homOfLE (Nat.le_succ n)).op)
  fac c j := pointedTowerLift_projection _ _ _ _ j.unop
  uniq c m hm := pointedTowerLimit_hom_ext X d (fun n ↦ by
    exact (hm (Opposite.op n)).trans
      (pointedTowerLift_projection X d (fun n ↦ c.π.app (Opposite.op n)) _ n).symm)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
