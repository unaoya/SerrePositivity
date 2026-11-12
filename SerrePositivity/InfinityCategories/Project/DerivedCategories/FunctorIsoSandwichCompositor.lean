module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoHorizontalNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoCancellationNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedNaturalityTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerMapTransport
/-!
概要：元の全体比較・中間同値の消去・合成子を同じ値で合成する。
方針：元の比較値と任意全関手射の可換四角形を保持する。
規約：追加の選択や可逆性を要求しない。使われ方：一般 cell 合成子の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "po" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
local notation "pr" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
def functorIsoSandwichCompositor {X A B Y C Z : SSet.{u}}
    (s : X ⟶ A) (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (h ≫ i) (𝟙 B))
    (F : X ⟶ Y) (G : Y ⟶ Z) (M : A ⟶ B) (N : B ⟶ C) (T : A ⟶ C)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (s ≫ M ≫ h)) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (i ≫ N ≫ t))
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (M ≫ N) T) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ G) (s ≫ T ≫ t) := by
  have d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((s ≫ M ≫ h) ≫ (i ≫ N ≫ t)) (s ≫ M ≫ N ≫ t) := by
    have q := (e.postcomp (N ≫ t)).precomp (s ≫ M)
    simpa only [Category.assoc, Category.id_comp] using! q
  have c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (s ≫ M ≫ N ≫ t) (s ≫ T ≫ t) := by
    have q := (k.postcomp t).precomp s
    simpa only [Category.assoc] using! q
  exact (a.postcomp G ≪≫ b.precomp (s ≫ M ≫ h)) ≪≫ d ≪≫ c
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
