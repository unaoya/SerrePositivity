module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.OppositeHomPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：元の固定射による全反転 Hom の作用を、元の豊穣後合成そのものへ戻す。
方針：固定射の全退化係数を豊穣 Hom の単位対象からの射と同定する。
規約：全ての次数で同じ固定射を保持。使われ方：三辺の native 値作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 片側を元の固定射に制限した全反転 Hom の合成は、同じ豊穣後合成の反転。 -/
lemma oppositeHomPrecomposition_fixed (x : C) {z y : C} (f : z ⟶ y) :
    lift (SSet.const (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' z y f)))
        (𝟙 (SimplicialCategory.sHom x z).op) ≫ oppositeHomPrecomposition x z y =
      SSet.opFunctor.map (eHomWhiskerLeft SSet x f) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  change (eComp SSet x z y).app (Opposite.op ⦋n⦌)
      (a, PinchedHom.constant (SimplicialCategory.homEquiv' z y f) n) =
    (eComp SSet x z y).app (Opposite.op ⦋n⦌)
      (a, (eHomEquiv SSet f).app (Opposite.op ⦋n⦌) PUnit.unit)
  congr 1
  apply Prod.ext
  · rfl
  · exact (unitHom_app_constant (eHomEquiv SSet f) n).symm

end SerrePositivity.InfinityCategories.F2
