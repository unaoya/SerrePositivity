module

public import SerrePositivity.InfinityCategories.Sheaves.SheafificationReflection
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf

/-!
概要：被覆篩と検出対象に添字を持つ小さい層生成辺族。
方針：G8の元の篩テンソル辺を同じ指定のまま使う。
使われ方：HTT 5.5.4.15・6.2.2.7、Kerodon Tag 06VH の反射へ渡す辺族。
規約：局所対象との一致は後続の定理で示す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]

/-- 同じ被覆篩の包含を、各検出対象との指定テンソルで送った辺族。 -/
def sheafGeneratingEdges (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {ι : Type u} (M : ι → E _⦋0⦌) :
    (Σ U : C, {S : Sieve U // S ∈ J U} × ι) → (PresheafCat C E) _⦋1⦌ :=
  fun ⟨_, S, i⟩ =>
    (SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sieveTensorEdge
      S.val hE (M i)).edge

end SerrePositivity.InfinityCategories.Sheaves
