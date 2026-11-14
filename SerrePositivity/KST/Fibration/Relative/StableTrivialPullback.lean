module
public import SerrePositivity.KST.Fibration.FamilyExactness
public import SerrePositivity.KST.Fibration.JointReflection
public import SerrePositivity.KST.SConstruction.SingleRealizationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement

/-!
概要：指定した trivial Kan 射に沿う安定模型の基底変換。
方針：元の SSet 引き戻しを使い、射影の完全性の反映で二射を完全にする。
規約：商関手や核述語には依存しない。使われ方：P 相対 cofiber の全補完。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の trivial Kan 射を順射とする完全な同値。
方針：既存の coherent な逆を完全性の不変性で持ち上げる。
規約：順射の変更なし。使われ方：補完・旗制限の実現比較。 -/
def stableTrivialEquivalence {E Y : StableModel.{u}} (p : E.carrier ⟶ Y.carrier)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] : StableModelEquivalence E Y := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration p
  let h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  let k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact { hom := ⟨p, h.preservesZero, h.preservesCofiber⟩
          inv := ⟨e.inv, k.preservesZero, k.preservesCofiber⟩
          homInvIso := e.homInvIso
          invHomIso := e.invHomIso }

/-- 概要：trivial Kan 射の基底変換の元の模型。
方針：射影に沿って安定性を輸送。規約：底の単体集合は実引き戻し。
使われ方：補完の選択全体を保持。 -/
def stableTrivialPullback {E Y T : StableModel.{u}} (p : E ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] (f : T ⟶ Y) : StableModel.{u} := by
  let a := pullback.snd p.val f.val
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _
  exact { carrier := pullback p.val f.val
          quasicategory := quasicategory_of_innerFibration a
          stable := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_trivialKanFibration a }

/-- 概要：基底変換の元の忘却射影。
方針：trivial Kan 射の完全性を使う。規約：同じ底への射。
使われ方：加法性比較の元の成分。 -/
def stableTrivialPullbackSnd {E Y T : StableModel.{u}} (p : E ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] (f : T ⟶ Y) : stableTrivialPullback p f ⟶ T := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd p.val f.val) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _
  exact ⟨pullback.snd p.val f.val, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber⟩

/-- 概要：基底変換の射影も trivial Kan。
方針：同じ指定射の基底変換。規約：SSet の全境界条件。
使われ方：完全な逆同値と実現比較。 -/
instance stableTrivialPullbackSnd_trivialKan {E Y T : StableModel.{u}} (p : E ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] (f : T ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (stableTrivialPullbackSnd p f).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

/-- 概要：保持した補完を抽出する完全な射。
方針：元の可換四角形と trivial Kan 射による完全性の反映。
規約：指定した p と f の四角形。使われ方：相対加法性の成分。 -/
def stableTrivialPullbackFst {E Y T : StableModel.{u}} (p : E ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] (f : T ⟶ Y) : stableTrivialPullback p f ⟶ E := by
  refine ⟨pullback.fst p.val f.val, ?_⟩
  apply preservesCofiberData_of_trivialProjection p.val
  rw [pullback.condition]
  exact (stableTrivialPullbackSnd p f ≫ f).property

/-- 概要：元の基底変換の完全な可換条件。
方針：引き戻しの条件。規約：局所化前の等式。
使われ方：共有端点引き戻しの貼り合わせ。 -/
lemma stableTrivialPullback_condition {E Y T : StableModel.{u}} (p : E ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] (f : T ⟶ Y) :
    stableTrivialPullbackFst p f ≫ p = stableTrivialPullbackSnd p f ≫ f :=
  Subtype.ext pullback.condition

/-- 概要：基底変換の補完成分と既存成分は共同で実普遍性を反映。
方針：共同反映を元の可換条件で引き戻し、trivial Kan 忘却で反映する。
規約：完全な元の二射。使われ方：相対 cofiber の有限旗への貼り合わせ。 -/
lemma stableTrivialPullback_jointReflection {E Y T X : StableModel.{u}}
    (p : E ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] (b : T ⟶ Y) (a : T ⟶ X)
    (h : JointlyReflectsSData a.val b.val) :
    JointlyReflectsSData (stableTrivialPullbackFst p b).val
      (stableTrivialPullbackSnd p b ≫ a).val := by
  constructor
  · intro v hv₀ hv₁
    apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration
      (stableTrivialPullbackSnd p b).val v).2
    apply h.zero _ hv₁
    have hp := p.property.1 _ hv₀
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((stableTrivialPullbackFst p b ≫ p).val.app _ v) at hp
    rw [stableTrivialPullback_condition] at hp
    exact hp
  · intro t ht₀ ht₁
    apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_iff_postcomp_trivialKanFibration
      (stableTrivialPullbackSnd p b).val t).2
    apply h.pushout _ ht₁
    have hp := (stableModelHom_preservesSConstructionData p).2 _ ht₀
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t ≫ (stableTrivialPullbackFst p b ≫ p).val) at hp
    rw [stableTrivialPullback_condition] at hp
    exact hp

end SerrePositivity.KST.Fibration.Relative
