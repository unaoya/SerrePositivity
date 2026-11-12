module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionCoreColimitDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionCoreFunctor

/-!
概要：底上の余極限に沿う section の core の制限錐は、実際の極限錐。
方針：任意のパラメーターを持つ族の貼り合わせと一意性を極限の普遍性へ束ねる。
規約：元の反変関手と元の余錐の全脚を使う。
使われ方：Kan fibration の制限図式による境界・セル・骨格の降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の底上の余錐へ section の core の制限関手を適用した錐。 -/
def cocartesianSectionCoreColimitCone {J : Type v} [Category.{w} J]
    {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p]
    {D : J ⥤ Over B} (c : Cocone D) :
    Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionCoreFunctor p ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionCoreFunctor p) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).mapCone c.op

/-- 錐の自然性は、元の各項上の core の族の厳密な整合性。 -/
lemma cocartesianSectionCoreCone_compatible {J : Type v} [Category.{w} J]
    {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (D : J ⥤ Over B)
    (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionCoreFunctor p ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))
    {j k : J} (f : j ⟶ k) :
    s.π.app (Opposite.op j) = s.π.app (Opposite.op k) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (D.map f)) :=
  (s.w f.op).symm

/-- 底上の余極限の section の core は、各項上の core の元の制限錐の極限。 -/
def cocartesianSectionCoreColimitCone_isLimit {J : Type v} [Category.{w} J] [Small.{u} J]
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {D : J ⥤ Over B} (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c)) :
    IsLimit (cocartesianSectionCoreColimitCone p c) where
  lift s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionCoreFamilyColimitLift p c hc
    (fun j ↦ s.π.app (Opposite.op j)) (cocartesianSectionCoreCone_compatible p D s)
  fac s j := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionCoreFamilyColimitLift_fac p c hc _ _ j.unop
  uniq s m hm := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionCoreFamilyColimitLift_unique
    intro j
    exact hm (Opposite.op j)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
