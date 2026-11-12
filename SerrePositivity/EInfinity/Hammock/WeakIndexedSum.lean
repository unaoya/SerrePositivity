module

public import SerrePositivity.EInfinity.Hammock.IndexedSum

/-!
# 元の任意の単体集合族の依存和の弱比較

概要：各項の元の射が弱同値なら、同じ添字の依存和の射も弱同値。
方針：元の添字への値の singleton 同型と有限支持の弱比較判定を使う。
規約：添字の有限性や非空性、元の各項の Kan 性は要求しない。
使われ方：元の全因子列の指定因子の比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.IndexedSum
open CategoryTheory SerrePositivity.InfinityCategories

lemma map_weak {I : Type u} {A B : I → SSet.{u}} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (f i)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (map f) := by
  apply ValueSupport.weak_of_singleton_restrictions (label A) (label B) (map f) (map_label f)
  intro i
  have hA := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (singletonIso A i)).isWeakHomotopyEquivalence
  have hB := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (singletonIso B i)).isWeakHomotopyEquivalence
  apply hB.cancel_right
  rw [singletonIso_naturality]
  exact hA.comp (hf i)

end SerrePositivity.EInfinity.Hammock.IndexedSum
