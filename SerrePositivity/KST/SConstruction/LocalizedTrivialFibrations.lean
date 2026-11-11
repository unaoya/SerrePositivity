module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-! # trivial Kan fibration の anodyne 局所化での可逆性
概要：anodyne 射を反転する任意の関手は trivial Kan fibration も反転する。
方針：厳密な切断と既存の全単射に対する持ち上げ性から実際の単体的ホモトピーを使う。
規約：値域モデル構造を仮定しない。使われ方：可縮な零段を一点へ潰す比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：anodyne 射を反転する関手は trivial Kan fibration を反転する。
方針：切断と実ホモトピーから像の逆同型を構成する。
規約：値域は任意の圏。使われ方：零段の射を一点への同値として使う。 -/
lemma map_isIso_of_trivialKanFibration {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] : IsIso (L.map p) :=
  MonoRightLiftingContraction.image_isIso p
    (fun _ _ i hi => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) i hi) L hL

end SerrePositivity.KST.SConstruction
