module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単体集合の逆向きの塔の極限と相対ホーン充填。
方針：各次数で整合族を取り、初段から帰納的に充填する。
規約：遷移の Kan fibration 性を使う。一般の厳密極限の Kan 性は仮定しない。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）、HTT A.3.3、BF 1978 §2。スペクトルの Hom。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.FibrationTower
end SerrePositivity.KST.Spectra.FibrationTower
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.FibrationTower

variable (X : ℕ → SSet.{u}) (d : ∀ n, X (n + 1) ⟶ X n)

/-- 概要：塔の極限を次数ごとの整合族で構成する。
方針：単体作用を成分ごとに定める。
規約：塔の遷移は n + 1 から n の向き。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）。充填を組み立てる極限。 -/
def limit : SSet.{u} where
  obj m := {s : ∀ n, (X n).obj m // ∀ n, (d n).app m (s (n + 1)) = s n}
  map f := ↾fun s ↦ ⟨fun n ↦ (X n).map f (s.val n), fun n ↦ by
    exact (NatTrans.naturality_apply (d n) f (s.val (n + 1))).trans
      (congrArg ((X n).map f) (s.property n))⟩
  map_id m := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    funext n
    exact ConcreteCategory.congr_hom ((X n).map_id m) (s.val n)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    funext n
    exact ConcreteCategory.congr_hom ((X n).map_comp f g) (s.val n)

/-- 概要：整合族から指定段への射影。
方針：各次数で成分を評価する。
規約：段の添字は自然数。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）。初段への fibration。 -/
def projection (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d ⟶ X n where
  app _ := ↾fun s ↦ s.val n

/-- 概要：極限の射影は塔の遷移と可換。
方針：整合族の条件を使う。
規約：厳密な等式。
使われ方：HTT A.3.3。極限の普遍性。 -/
@[reassoc (attr := simp)]
theorem projection_comp (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d (n + 1) ≫ d n = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d n := by
  ext m s
  exact s.property n

/-- 概要：整合する射の族を極限へ持ち上げる。
方針：入力した射を各段の成分に取る。
規約：任意の始域 A。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）。段ごとの充填の組み立て。 -/
def lift {A : SSet.{u}} (f : ∀ n, A ⟶ X n) (hf : ∀ n, f (n + 1) ≫ d n = f n) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d where
  app m := ↾fun a ↦ ⟨fun n ↦ (f n).app m a, fun n ↦ by
    exact congrArg (fun k : A ⟶ X n ↦ k.app m a) (hf n)⟩
  naturality a b g := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    funext n
    exact NatTrans.naturality_apply (f n) g s

/-- 概要：極限への持ち上げを射影すると指定成分になる。
方針：次数ごとの定義を計算する。
規約：整合性の証明の選択に依存しない。
使われ方：HTT A.3.3。塔の充填の計算。 -/
@[reassoc (attr := simp)]
theorem lift_projection {A : SSet.{u}} (f : ∀ n, A ⟶ X n)
    (hf : ∀ n, f (n + 1) ≫ d n = f n) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift X d f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d n = f n := rfl

/-- 概要：極限への射は全ての成分で決まる。
方針：整合族の外延性を使う。
規約：任意の始域 A。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）。充填の境界等式。 -/
theorem hom_ext {A : SSet.{u}} {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d}
    (h : ∀ n, f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d n = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d n) : f = g := by
  ext m a
  apply Subtype.ext
  funext n
  exact congrArg (fun k : A ⟶ X n ↦ k.app m a) (h n)

section Lifting

variable {A B : SSet.{u}} (j : A ⟶ B) [∀ n, HasLiftingProperty j (d n)]
  (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d) (b : B ⟶ X 0) (sq : CommSq a j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0) b)

/-- 概要：初段の指定充填から各段への拡張を帰納的に選ぶ。
方針：一つ前の拡張を底として遷移の右持ち上げ性を使う。
規約：全ての段で同じ左射 j を用いる。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）。塔の相対充填の構成。 -/
noncomputable def stages : ∀ n, {f : B ⟶ X n // j ≫ f = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d n}
  | 0 => ⟨b, sq.w.symm⟩
  | n + 1 =>
    let prev := stages n
    let s : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d (n + 1)) j (d n) prev.val :=
      ⟨by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp, prev.property]⟩
    ⟨s.lift, s.fac_left⟩

/-- 概要：帰納的に選んだ拡張は隣接段の遷移と整合する。
方針：各段の相対持ち上げの底辺の等式を使う。
規約：証明の選択は stages に固定する。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）。拡張を極限へ組み立てる。 -/
theorem stages_comp (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.stages X d j a b sq (n + 1)).val ≫ d n = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.stages X d j a b sq n).val := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.stages]
  exact CommSq.fac_right _

end Lifting

/-- 概要：遷移が右持ち上げ性を持つ塔の初段射影も同じ性質を持つ。
方針：帰納的な相対充填を整合族の極限へ組み立てる。
規約：任意の左射 j。モデル構造は不要。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）、HTT A.3.3。Hom の塔の fibration。 -/
theorem projection_zero_hasLiftingProperty {A B : SSet.{u}} (j : A ⟶ B)
    [∀ n, HasLiftingProperty j (d n)] : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0) := by
  constructor
  intro a b sq
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.stages X d j a b sq
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift X d (fun n ↦ (f n).val) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.stages_comp X d j a b sq)
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext X d
    intro n
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection]
    exact (f n).property
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection X d _ _ 0

/-- 概要：Kan fibration の塔の初段射影は Kan fibration。
方針：全てのホーンに対する右持ち上げ性を移す。
規約：遷移の fibration 性だけを使う。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）、BF 1978 §2。写像空間の塔。 -/
@[kerodon 03HU]
theorem projection_zero_fibration [∀ n, Fibration (d n)] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B j hj
  let : ∀ n, HasLiftingProperty j (d n) := fun n ↦
    ((SSet.modelCategoryQuillen.fibration_iff (d n)).mp inferInstance) j hj
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_zero_hasLiftingProperty X d j

/-- 概要：Kan な初段と fibration の遷移を持つ塔の極限は Kan。
方針：初段射影と終対象への fibration を合成する。
規約：任意の厳密極限に対する主張ではない。
使われ方：Kerodon Corollary 11.9.7.2（Tag 01C7）、HTT A.3.3。スペクトルの Hom の Kan 性。 -/
@[kerodon 03HU]
instance limit_kanComplex [∀ n, Fibration (d n)] [KanComplex (X 0)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d) := by
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_zero_fibration X d
  change Fibration (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d))
  rw [show terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0 ≫ terminal.from (X 0) from
    Subsingleton.elim _ _]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
