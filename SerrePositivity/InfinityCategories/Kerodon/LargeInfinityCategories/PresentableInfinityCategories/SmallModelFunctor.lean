module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactModels
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EquivalenceDescent

/-!
概要：小さい模型の間へ元の関手を移し、元の関手との全自然な比較を与える。
方針：二つの全同値で共役し、ULift の完全忠実性で小さい宇宙へ戻す。
規約：比較は頂点だけでなく全パラメーターの関手同型とする。
使われ方：compact 成分の cospan を小さい ∞ 圏の図式として扱う。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：小さい全同値模型に移した関手。
方針：模型の順方向、元の関手、標的模型の逆方向を合成して宇宙を降ろす。
規約：元の圏に固定頂点写像の小ささを仮定しない。
使われ方：小さい compact 成分の cospan の辺。 -/
def smallModelFunctor {A B : SSet.{u}} {C D : SSet.{u + 1}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory D]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) C)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj B) D) (G : C ⟶ D) : A ⟶ B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (e.hom ≫ G ≫ f.inv)

/-- 概要：移した小さい関手の宇宙持ち上げは指定した共役関手に一致する。
方針：ULift の射の降下と持ち上げの往復公式を適用する。
規約：全単体での射の等式。
使われ方：小さい図式と元の図式の比較の構成。 -/
lemma smallModelFunctor_lift {A B : SSet.{u}} {C D : SSet.{u + 1}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory D]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) C)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj B) D) (G : C ⟶ D) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallModelFunctor e f G) = e.hom ≫ G ≫ f.inv :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _

/-- 概要：移した関手を模型から戻すと元の関手に全自然に同型となる。
方針：共役の標的側の全同値の余単位を前合成する。
規約：元の関手と模型の包含を同じ始域で比較する。
使われ方：小さい compact cospan と元の cospan の比較。 -/
def smallModelFunctor_comparison {A B : SSet.{u}} {C D : SSet.{u + 1}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory D]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) C)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj B) D) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map (smallModelFunctor e f G) ≫ f.hom)
      (e.hom ≫ G) := by
  rw [smallModelFunctor_lift]
  simpa only [Category.assoc, Category.comp_id] using f.invHomIso.precomp (e.hom ≫ G)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
