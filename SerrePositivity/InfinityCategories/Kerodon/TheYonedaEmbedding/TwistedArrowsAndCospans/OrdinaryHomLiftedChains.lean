module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomJoinReindex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
概要：Hom の join 射列を、標準単体の nerve に使う持ち上げた有限順序集合へ移す。
方針：同じ順序同型による下降関手を左右に前合成し、全再添字を比較する。
規約：Hom の射列を作り直さず、既存の普通の join 射列をそのまま使う。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の模型比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {m n : ℕ}

/-- 標準単体の nerve の添字を元の有限順序集合へ戻す指定関手。
Kerodon Proposition 8.1.1.10（Tag 03JN）、添字の宇宙移送の法則の入力。 -/
def homChainIndexDown (n : ℕ) : ULift.{u} (Fin (n + 1)) ⥤ Fin (n + 1) :=
  ULift.orderIso.toOrderEmbedding.toOrderHom.monotone.functor

/-- 有限順序写像を同じ持ち上げた順序集合の間へ移す。
Kerodon Proposition 8.1.1.10（Tag 03JN）、添字の宇宙移送の法則の入力。 -/
def homChainIndexMap (α : Fin (m + 1) →o Fin (n + 1)) :
    ULift.{u} (Fin (m + 1)) ⥤ ULift.{u} (Fin (n + 1)) :=
  (ULift.orderIso.symm.toOrderEmbedding.toOrderHom.comp
    (α.comp ULift.orderIso.toOrderEmbedding.toOrderHom)).monotone.functor

/-- 同じ添字の下降と再添字は厳密に可換。
Kerodon Proposition 8.1.1.10（Tag 03JN）、添字の宇宙移送則。 -/
lemma homChainIndexMap_down (α : Fin (m + 1) →o Fin (n + 1)) :
    homChainIndexMap.{u} α ⋙ homChainIndexDown n = homChainIndexDown m ⋙ α.toFunctor := rfl

/-- 持ち上げた添字で読んだ同じ Hom の join 射列。
Kerodon Proposition 8.1.1.10（Tag 03JN）、元の射列から標準単体への係数移送。 -/
def ordinaryHomLiftedJoinChain (s : ComposableArrows (OrdinaryHomElements C) n) :
    CategoryTheory.Join (ULift.{u} (Fin (n + 1)))ᵒᵖ (ULift.{u} (Fin (n + 1))) ⥤ C :=
  CategoryTheory.Join.mapPair (homChainIndexDown n).op (homChainIndexDown n) ⋙
    ordinaryHomJoinChain s

/-- 持ち上げた Hom の join 射列も、全再添字と厳密に可換。
Kerodon Proposition 8.1.1.10（Tag 03JN）、左右の全射列の宇宙移送則。 -/
lemma ordinaryHomLiftedJoinChain_reindex
    (s : ComposableArrows (OrdinaryHomElements C) n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    CategoryTheory.Join.mapPair (homChainIndexMap.{u} α).op (homChainIndexMap.{u} α) ⋙
        ordinaryHomLiftedJoinChain s =
      ordinaryHomLiftedJoinChain (α.toFunctor ⋙ s) := by
  refine CategoryTheory.Functor.hext (fun x => by cases x <;> rfl) ?_
  intro x y f
  cases f using CategoryTheory.Join.homInduction with
  | left a b f => rfl
  | right a b f => rfl
  | edge a b =>
    exact heq_of_eq (ordinaryHomCrossChain_reindex s α a.unop.down b.down).symm

/-- 標準単体と持ち上げた有限順序集合の nerve の指定同型は全再添字と可換。
Kerodon Proposition 8.1.1.10（Tag 03JN）、標準単体の模型移送の法則。 -/
lemma homChainIndexNerve_naturality (α : ⦋m⦌ ⟶ ⦋n⦌) :
    stdSimplex.map α ≫ (stdSimplex.isoNerve.{u} n).hom =
      (stdSimplex.isoNerve.{u} m).hom ≫ nerveMap (homChainIndexMap.{u} α.toOrderHom) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro i j h
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
