module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedRepresentableComparison
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：任意の錐の厳密極限への射と単体集合の反転の厳密な整合性。
方針：反転の極限保存同型の全射影を比較し、二重反転の同型で同値性を戻す。
規約：錐自体の極限性は要求しない。
使われ方：HTT 4.2.4.1 の限定形、元の q_x と反転した q′ の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedConeLimitLift
noncomputable section

local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 概要：Kan 複体間の単体的ホモトピー同値性は単体集合の反転で検出できる。
方針：反転を二回適用し、二重反転の自然同型で元の射へ戻す。
規約：反転の保存側にも両端の Kan 性を使う。
使われ方：元の厳密極限への射と反転した射の同値判定。 -/
lemma oppositeKanHomotopyEquivalence_iff {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (SSet.opFunctor.map f) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  constructor
  · intro h
    have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence h
    let eX : X.op.op ≅ X := SSet.opFunctorCompOpFunctorIso.app X
    let eY : Y.op.op ≅ Y := SSet.opFunctorCompOpFunctorIso.app Y
    have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso eX.inv).comp
      (h₂.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso eY.hom))
    have hn : SSet.opFunctor.map (SSet.opFunctor.map f) ≫ eY.hom = eX.hom ≫ f :=
      SSet.opFunctorCompOpFunctorIso.hom.naturality f
    rw [hn, Iso.inv_hom_id_assoc] at hh
    exact hh
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence

/-- 概要：任意の錐の厳密極限への射は反転の極限保存同型と可換。
方針：反転した極限の全射影で持ち上げの成分を計算する。
規約：錐の極限性や Kan 性は不要。
使われ方：q_x と q′ の分解の中間射の直接の比較。 -/
lemma reflectedConeLimitLift {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}}
    (c : Cone H) :
    SSet.opFunctor.map (limit.lift H c) ≫ (preservesLimitIso SSet.opFunctor H).hom =
      limit.lift (H ⋙ SSet.opFunctor) (SSet.opFunctor.mapCone c) := by
  apply limit.hom_ext
  intro i
  rw [Category.assoc, preservesLimitIso_hom_π, ← Functor.map_comp, limit.lift_π, limit.lift_π]
  rfl

/-- 概要：任意の Kan な頂点の錐の厳密極限への射の同値性は反転した錐でも同じ。
方針：極限保存同型の後合成を消去し、反転による同値性の検出を使う。
規約：頂点と元の厳密極限の Kan 性を明示し、錐の極限性は要求しない。
使われ方：指定三形状の元の標準比較と反転標準比較の同値判定。 -/
lemma reflectedConeLimitLift_homotopyEquivalence_iff
    {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [KanComplex (limit H)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (limit.lift (H ⋙ SSet.opFunctor) (SSet.opFunctor.mapCone c)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (limit.lift H c) := by
  have : KanComplex (limit (H ⋙ SSet.opFunctor)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (preservesLimitIso SSet.opFunctor H)
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (preservesLimitIso SSet.opFunctor H).hom
  constructor
  · intro h
    rw [← reflectedConeLimitLift c] at h
    exact (oppositeKanHomotopyEquivalence_iff _).mp (hi.cancel_right h)
  · intro h
    rw [← reflectedConeLimitLift c]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence h).comp hi

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedConeLimitLift
