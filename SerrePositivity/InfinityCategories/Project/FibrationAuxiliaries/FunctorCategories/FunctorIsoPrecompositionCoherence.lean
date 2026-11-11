module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：関手同型の前合成と合成・等式の移送の整合性。
方針：前合成を関手空間の射による頂点同型の像として計算する。
規約：始点と終点を固定した同型そのものの等式。
使われ方：族の余単位の端点の移送とパラメーター制限を整理する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：関手同型の前合成は同型の合成を保つ。
方針：前合成を頂点同型の像と表示する。
規約：三つの関手を同時に同じ射で前合成する。
使われ方：余単位と端点の移送の合成を制限する。 -/
lemma FunctorIso.precomp_trans {A B X : SSet.{u}} {f g h : B ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) (i : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (e ≪≫ d) i = e.precomp i ≪≫ d.precomp i := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (e ≪≫ d) ((pre i).app X) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e ((pre i).app X) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map d ((pre i).app X)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans e d ((pre i).app X)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (precomp_trans)


/-- 概要：図式の等式による同型の前合成は制限後の等式の同型。
方針：等式を消去し恒等同型の像を計算する。
規約：等式の移送を独立に選んだ同型へ置き換えない。
使われ方：curry の往復の等式を制限する。 -/
lemma FunctorIso.precomp_eqToIso {A B X : SSet.{u}} {f g : B ⟶ X}
    (h : f = g) (i : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
      (eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)) h)) i =
      eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ d))) h) := by
  subst g
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (Iso.refl _) ((pre i).app X) = Iso.refl _
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (precomp_eqToIso)


/-- 概要：関手同型の前合成は逆同型を保つ。
方針：前合成を同じ頂点同型の像として計算する。
規約：逆向きの比較を独立に選ばない。
使われ方：余単位の自然性を単位側へ移す。 -/
lemma FunctorIso.precomp_symm {A B X : SSet.{u}} {f g : B ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (i : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm i = (e.precomp i).symm := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e.symm ((pre i).app X) = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e ((pre i).app X)).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_symm e ((pre i).app X)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (precomp_symm)


end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
