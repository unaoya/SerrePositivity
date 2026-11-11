module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianSquare
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：底の余極限の各項上の表現条件から全体の表現条件を反映する。
方針：余極限の脚が全頂点を被覆し、各 pullback 脚が fiber 同型を与えることを使う。
規約：全空間側の写像と分類図式をともに固定した四角形を判定する。
使われ方：貼り合わせた四角形を実際の表現へ戻す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底の余極限の pullback 脚での表現条件は全体の表現条件を反映する。
方針：各頂点を余極限の脚で持ち上げ fiber 同型による判定を使う。
規約：余極限の脚の単射性は不要。
使われ方：表現空間の余極限に沿う降下。 -/
lemma LeftTransportSquare.isRepresentation_of_colimit
    {J : Type v} [Category.{w} J] [Small.{u + 1} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration c.pt.hom] [∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (D.obj j).hom]
    (hc : IsColimit (Arrow.rightFunc.mapCocone c))
    (hp : ∀ j, IsPullback (c.ι.app j).left (D.obj j).hom c.pt.hom (c.ι.app j).right)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare c.pt.hom) (hS : ∀ j, (S.preSquare (c.ι.app j)).IsRepresentation) :
    S.IsRepresentation := by
  intro b
  let ev := (evaluation SimplexCategoryᵒᵖ (Type (u + 1))).obj (Opposite.op ⦋0⦌)
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective _ (isColimitOfPreserves ev hc) b
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (S.pointedFiberMap ((c.ι.app j).right.app _ x)) :=
    (S.preSquare_pointedFiberMap_isQCatEquivalence_iff (c.ι.app j) (hp j) x).mp (hS j x)
  change (c.ι.app j).right.app (Opposite.op ⦋0⦌) x = b at hx
  rw [hx] at h
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportSquare (isRepresentation_of_colimit)


/-- 概要：底の余極限の各 pullback 脚で表現となる頂点は全体で表現の頂点。
方針：頂点の実際の四角形を回収して表現条件を反映する。
規約：表現の頂点を新たに選び直さない。
使われ方：全高次の錐の貼り合わせを全部分複体へ持ち上げる。 -/
lemma isTransportWitnessVertex_of_colimit {J : Type v} [Category.{w} J] [Small.{u + 1} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration c.pt.hom] [∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (D.obj j).hom]
    (hc : IsColimit (Arrow.rightFunc.mapCocone c))
    (hp : ∀ j, IsPullback (c.ι.app j).left (D.obj j).hom c.pt.hom (c.ι.app j).right)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace c.pt.hom) _⦋0⦌)
    (hv : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex (D.obj j).hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre (c.ι.app j)).app _ v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex c.pt.hom v := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareOfVertex c.pt.hom v
  have hS : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S = v := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_ofVertex c.pt.hom v
  rw [← hS]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.isTransportWitnessVertex_iff_isRepresentation c.pt.hom S).mpr
  apply S.isRepresentation_of_colimit c hc hp
  intro j
  have h := hv j
  rw [← hS, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.isTransportWitnessVertex_iff_isRepresentation] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
