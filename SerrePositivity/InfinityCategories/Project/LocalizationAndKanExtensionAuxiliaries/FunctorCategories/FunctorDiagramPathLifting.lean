module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeEquivalencePath

/-!
概要：制限された図式の可逆 path を、既定の部分族を保って元の図式へ持ち上げる。
方針：関手単体集合の制限の相対可逆 path 写像の全単射に対する持ち上げを使う。
規約：境界の path 自体を保ち、その終点の同型だけに置き換えない。
使われ方：基準三角形の合成辺を導来 fiber の path に沿って動かす相対構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：単射に沿う図式制限の可逆 path は、既定の部分族と始点の図式を保って持ち上がる。
方針：path と始点の引き戻しへ写し、相対 path 写像の trivial Kan fibration 性を使う。
規約：A,B,S,T の quasicategory 性は不要。制限後の path の全体を厳密に保つ。
使われ方：逆向きの比較とその両合成のホモトピーを相対的に構成する一般の持ち上げ。 -/
lemma exists_functorDiagramPath_lift_relative {A B S T X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (j : S ⟶ T) [Mono j]
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom A).obj X))
    (b : T ⟶ (ihom B).obj X)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = b ≫ (pre i).app X)
    (l : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom B).obj X))
    (hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) = j ≫ a)
    (hb : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = j ≫ b) :
    ∃ L : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom B).obj X),
      j ≫ L = l ∧
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) = a ∧
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = b := by
  let p := (pre i).app X
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMap p
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_relativeEquivalencePathMap_pre i X
  let t : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathTarget p := pullback.lift a b h
  have hs : CommSq l j q t := by
    constructor
    apply pullback.hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMap_fst, Category.assoc, pullback.lift_fst]
      exact hl
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMap_snd, Category.assoc, pullback.lift_snd]
      exact hb
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := q) j inferInstance
  refine ⟨hs.lift, hs.fac_left, ?_, ?_⟩
  · calc
      _ = (hs.lift ≫ q) ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0) p := by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMap_fst]
      _ = a := by rw [hs.fac_right]; exact pullback.lift_fst _ _ _
  · calc
      _ = (hs.lift ≫ q) ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0) p := by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMap_snd]
      _ = b := by rw [hs.fac_right]; exact pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
