module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutProduct

/-!
概要：単射と trivial Kan fibration による相対内部 Hom の全境界持ち上げ。
方針：内部 Hom の持ち上げを pushout-product の単射に対する持ち上げに移す。
規約：trivial Kan fibration は既存の全単射の rlp のみを使う。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の相対 path の持ち上げ。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：単射と trivial Kan fibration の相対内部 Hom は trivial Kan fibration。
方針：境界と単射の pushout-product は単射であることと二変数随伴を使う。
規約：元の四対象の quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の可逆 path の制限。 -/
lemma trivialKanFibration_pullbackObjObjπ {A B E Y : SSet.{u}}
    (i : A ⟶ B) [Mono i] (p : E ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (sq' : internalHom.PullbackObjObj i p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq'.π := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i (boundary n).ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) sq.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.mono_pushoutObjObj_ι i (boundary n).ι sq)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
