module
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.KST.SConstruction.DGModuleClosedExactInclusion
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorExact

/-! # 実 Perf dg 延長の完全性
概要：厳密 dg 関手の実 Perf 延長の native nerve は完全である。
方針：元の包含との可換性から、周囲の cofiber 保存を充満 dg 部分圏へ反映する。
規約：任意の元の cofiber 列を保持する。使われ方：K-4d の S 構成上の射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories DGNerve
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D E)

/-- 実 Perf dg 延長の nerve は、元の全 cofiber 列を保存する。 -/
lemma perfectDGExtensionNerve_isExactFunctor :
    IsExactFunctor (dgNerve.map (perfectDGExtension A D E F)) where
  preservesZero := dgFunctorNerve_preservesZeroVertices _
  preservesCofiber t ht := by
    let i := perfectDGModuleInclusion A D Set.univ
    let : IsExactFunctor (dgNerve.map i) :=
      dgModuleClosedInclusion_isExactFunctor A D _ (perfectDGClosedOperations A D Set.univ)
    let := dgModuleFunctorNerve_isExactFunctor A D E (dgModuleExtension A D E F)
    apply isColimitCone_of_fullInclusion A (RightModule A E)
      (modulePerfectProjectiveOver A E Set.univ) (pushoutCocone _)
    change IsPushoutSquare ((t.square ≫ dgNerve.map (perfectDGExtension A D E F)) ≫
      dgNerve.map (perfectDGModuleInclusion A E Set.univ))
    rw [Category.assoc, ← dgNerve.map_comp, perfectDGExtension_inclusion, dgNerve.map_comp,
      ← Category.assoc]
    exact IsExactFunctor.preservesCofiber
      (t.map (dgNerve.map i) (dgFunctorNerve_preservesZeroVertices i))
      (IsExactFunctor.preservesCofiber t ht)

/-- 元の厳密 dg 関手から得た実 Perf 延長を、K の安定入力間の射にする。 -/
def perfectDGStableMap : perfectDGStableModel A D Set.univ ⟶
    perfectDGStableModel A E Set.univ := by
  let := perfectDGExtensionNerve_isExactFunctor A D E F
  exact ⟨dgNerve.map (perfectDGExtension A D E F), preservesCofiberData_of_isExactFunctor _⟩

end SerrePositivity.KST.SConstruction
