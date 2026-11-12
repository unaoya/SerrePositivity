module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：通常の恒等射の豊穣頂点への定値族を、同じ豊穣単位と同定する。
方針：単位からの射の定値単体式と通常の恒等射との対応を使う。
規約：パラメーター単体集合は任意。
使われ方：第二三角形の同じラベル内の Hom の照合。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 通常の恒等射の頂点への定値族は、元の豊穣恒等射の定値族。 -/
lemma simplicialHom_const_id {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X : C) {T : SSet.{u}} :
    (SSet.const (SimplicialCategory.homEquiv' X X (𝟙 X)) : T ⟶ _) = toUnit T ≫ eId SSet X := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X X (𝟙 X)) n =
    (eId SSet X).app (Opposite.op ⦋n⦌) PUnit.unit
  simpa only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eId SSet X) n).symm

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
