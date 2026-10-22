module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoHorizontalNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoCancellationNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedNaturalityTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerMapTransport
/-!
概要：元の全体比較・中間同値の消去・合成子を同じ値で合成する。
方針：元の比較値と任意全関手射の可換四角形を保持する。
規約：追加の選択や可逆性を要求しない。使われ方：一般 cell 合成子の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "po" => functorHomPostcomp
local notation "pr" => functorHomPrecomp
def functorIsoSandwichCompositor {X A B Y C Z : SSet.{u}}
    (s : X ⟶ A) (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z)
    (e : FunctorIso (h ≫ i) (𝟙 B))
    (F : X ⟶ Y) (G : Y ⟶ Z) (M : A ⟶ B) (N : B ⟶ C) (T : A ⟶ C)
    (a : FunctorIso F (s ≫ M ≫ h)) (b : FunctorIso G (i ≫ N ≫ t))
    (k : FunctorIso (M ≫ N) T) : FunctorIso (F ≫ G) (s ≫ T ≫ t) := by
  have d : FunctorIso ((s ≫ M ≫ h) ≫ (i ≫ N ≫ t)) (s ≫ M ≫ N ≫ t) := by
    have q := (e.postcomp (N ≫ t)).precomp (s ≫ M)
    simpa only [Category.assoc, Category.id_comp] using! q
  have c : FunctorIso (s ≫ M ≫ N ≫ t) (s ≫ T ≫ t) := by
    have q := (k.postcomp t).precomp s
    simpa only [Category.assoc] using! q
  exact (a.postcomp G ≪≫ b.precomp (s ≫ M ≫ h)) ≪≫ d ≪≫ c
end
end SerrePositivity.InfinityCategories
