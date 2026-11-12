module

public import SerrePositivity.KST.Spectra.KanSequenceMappingExchange

/-!
概要：全列のパラメータ族を、同じ内部 Hom パラメータを保つ mapping 列の族へ移す。
方針：元の列射へ mapping を施し、二重 mapping 列の厳密交換を後合成する。
規約：パラメータの Kan 性不要。使われ方：符号付き loop 列の全パラメータ作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 元のパラメータ付き列射を、mapping 列のパラメータ付き列射へ移す。 -/
def mappingParameterHom (K : PointedSimplicialSet.{u}) {A : PointedSimplicialSet.{u}}
    {X Y : KanSequence.{u}} (f : Hom X (mapping A Y)) :
    Hom (mapping K X) (mapping A (mapping K Y)) :=
  (mappingPost K f).comp (mappingExchange K A Y)

/-- 全列作用の各段は、元の射への mapping と同じ内部 Hom 交換そのもの。 -/
lemma mappingParameterHom_app (K : PointedSimplicialSet.{u}) {A : PointedSimplicialSet.{u}}
    {X Y : KanSequence.{u}} (f : Hom X (mapping A Y)) (n : ℕ) :
    (mappingParameterHom K f).app n = (ihom K).map (f.app n) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K A (Y.level n).space).hom := rfl

/-- 元の mapping パラメータへの制限は、全列の族の作用と厳密に可換。 -/
lemma mappingParameterHom_pre {K' K A : PointedSimplicialSet.{u}} (i : K' ⟶ K)
    {X Y : KanSequence.{u}} (f : Hom X (mapping A Y)) :
    (mappingPre i X).comp (mappingParameterHom K' f) =
      (mappingParameterHom K f).comp (mappingPost A (mappingPre i Y)) := by
  apply Hom.ext_app
  intro n
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space ≫
      ((ihom K').map (f.app n) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K' A (Y.level n).space).hom) =
    ((ihom K).map (f.app n) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K A (Y.level n).space).hom) ≫
      (ihom A).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (Y.level n).space)
  have hn := (MonoidalClosed.pre i).naturality (f.app n)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  rw [← Category.assoc]
  erw [← hn]
  rw [Category.assoc]
  have he := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left i A (Y.level n).space
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at he
  erw [he]
  rw [Category.assoc]

end SerrePositivity.KST.Spectra.KanSequence
