module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.MapHomotopyCategoryComp
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerUnit

/-!
分割で生成：docstring を書き直すこと
概要：指定同型の二段の前合成と、標的表示の往復を指定値を保って簡約する。
方針：関手空間の前合成の合成則と、明示した同型の往復の等式を使う。
規約：端点を明示して指定類を保持。使われ方：共通の左脚の底の指定像の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 指定同型の二段の前合成は、元の合成射による前合成そのものである。 -/
lemma functorIso_precomp_precomp {A B X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : B ⟶ X) (q : A ⟶ B) :
    (e.precomp p).precomp q = e.precomp (q ≫ p) := by
  have hn : (pre (q ≫ p)).app Y = (pre p).app Y ≫ (pre q).app Y := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    rfl
  have hh := congrArg (fun k => SSet.mapHomotopyCategory k) hn
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapHomotopyCategory_comp_eq] at hh
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  exact (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq hh e)).symm

/-- 元の前合成射の等式は指定同型の前合成の値を型付きで保つ。 -/
lemma functorIso_precomp_heq_of_map_eq {A X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) {p q : A ⟶ X} (h : p = q) :
    HEq (e.precomp p) (e.precomp q) := by cases h; rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
