module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFamilyUnderlying
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
概要：通常の関手の fiber の nerve と単体集合の vertex fiber を比較する。
方針：図式が定値な射列を通常の fiber の関手へ持ち上げる。
規約：同じ宇宙の小さい圏と単体集合を扱う。
使われ方：B5 の通常の錐と native な錐の族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {D E : Type u} [Category.{u} D] [Category.{u} E] (p : D ⥤ E) (e : E)

/-- 概要：通常の functor fiber の nerve を vertex fiber へ写す。
方針：図式が定値な射列を通常の fiber の関手へ持ち上げる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def nerveFunctorFiberMap :
    nerve (Functor.Fiber p e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (nerveMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (nerveMap (Functor.Fiber.fiberInclusion (p := p) (S := e))) (by
    change nerveMap (Functor.Fiber.fiberInclusion ⋙ p) = _
    rw [Functor.Fiber.fiberInclusion_comp_eq_const, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveMap_const])

/-- 概要：vertex fiber の各単体を通常の functor fiber の射列へ戻す。
方針：図式が定値な射列を通常の fiber の関手へ持ち上げる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def nerveFunctorFiberRead {n : ℕ}
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (nerveMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex e)) _⦋n⦌) :
    ComposableArrows (Functor.Fiber p e) n :=
  Functor.Fiber.inducedFunctor (show σ.val ⋙ p = (Functor.const (Fin (n + 1))).obj e from
    σ.property)

/-- 概要：読み戻した射列を写すと元の vertex fiber の単体になる。
方針：図式が定値な射列を通常の fiber の関手へ持ち上げる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma nerveFunctorFiberMap_read {n : ℕ}
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (nerveMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex e)) _⦋n⦌) :
    (nerveFunctorFiberMap p e).app _ (nerveFunctorFiberRead p e σ) = σ := by
  apply Subtype.ext
  rfl

/-- 概要：写した単体から元の functor fiber の射列を回収する。
方針：図式が定値な射列を通常の fiber の関手へ持ち上げる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma nerveFunctorFiberRead_map {n : ℕ} (σ : (nerve (Functor.Fiber p e)) _⦋n⦌) :
    nerveFunctorFiberRead p e ((nerveFunctorFiberMap p e).app _ σ) = σ := by
  let ho :
      ∀ i, (nerveFunctorFiberRead p e ((nerveFunctorFiberMap p e).app _ σ)).obj i = σ.obj i :=
    fun i ↦ Subtype.ext rfl
  refine CategoryTheory.Functor.ext ho (fun i j f ↦ ?_)
  apply Subtype.ext
  change (σ.map f).val =
    (Functor.Fiber.fiberInclusion (p := p) (S := e)).map (eqToHom (ho i)) ≫
      (σ.map f).val ≫ (Functor.Fiber.fiberInclusion (p := p) (S := e)).map (eqToHom (ho j).symm)
  rw [eqToHom_map, eqToHom_map]
  simp only [eqToHom_refl, Category.id_comp]
  exact (Category.comp_id _).symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
