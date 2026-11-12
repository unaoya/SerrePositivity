module
public import SerrePositivity.KST.SConstruction.Cofinality.CutCokernelEquiv
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagDiscreteness
public import SerrePositivity.KST.Spectra.GroupNerveCoordinates

/-!
概要：採用済み Sp-8 (2) の群 nerve の高次消滅を明示入力として受ける。
方針：一般供給の命題を保ち、元の S 余核の群へ代入する。
規約：一般供給を公理や instance として宣言しない。
使われ方：障害余核の bar 同定後の高次ホモトピー消滅。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：一般の群 nerve の二次以上のホモトピー消滅の供給仕様。
方針：同じ連続 Kan 置換の実ホモトピー類を使う。
規約：Sp-8 (2) 到着まで明示的な仮定引数として保持する。
使われ方：K-cof の元の余核群への一般供給の代入。 -/
def GroupNerveHigherVanishingInput : Prop :=
  ∀ (G : Type u) (_ : Group G) (n : ℕ), 1 < n →
    ∀ x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (nerve (AsSmall.{u} (SingleObj G)))) _⦋0⦌,
      Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (nerve (AsSmall.{u} (SingleObj G)))) n x)

/-- 概要：元の指定 S 射の K₀ 余核の bar の二次以上のホモトピー消滅。
方針：明示的な一般入力に元の余核群を代入する。
規約：余核図式そのものと bar の同定は別途必要。
使われ方：同定済みの障害 bar の消滅を相対 fiber へ渡す入口。 -/
lemma cutCokernelBar_higher_of_input (h : GroupNerveHigherVanishingInput.{u})
    (m : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      (nerve (AsSmall.{u} (SingleObj (Multiplicative (cutKZeroCokernel m f)))))) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
        (nerve (AsSmall.{u} (SingleObj (Multiplicative (cutKZeroCokernel m f)))))) n x) :=
  h (Multiplicative (cutKZeroCokernel m f)) inferInstance n hn x

end SerrePositivity.KST.SConstruction.Cofinality
