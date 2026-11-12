module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.FunctorFiberMap
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：通常の functor fiber の nerve を native な vertex fiber と同型にする。
方針：全次数での射列の往復を同型へまとめる。
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

/-- 概要：functor fiber と vertex fiber の比較は各次数で全単射。
方針：全次数での射列の往復を同型へまとめる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def nerveFunctorFiberObjEquiv (n : ℕ) : (nerve (Functor.Fiber p e)) _⦋n⦌ ≃
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (nerveMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex e)) _⦋n⦌ where
  toFun := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorFiberMap p e).app _
  invFun := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorFiberRead p e
  left_inv := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorFiberRead_map p e
  right_inv := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorFiberMap_read p e

/-- 概要：functor fiber の nerve からの比較射は同型。
方針：全次数での射列の往復を同型へまとめる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
instance nerveFunctorFiberMap_isIso : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorFiberMap p e) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).2 (nerveFunctorFiberObjEquiv p e n).bijective

/-- 概要：functor fiber の nerve と vertex fiber の指定同型。
方針：全次数での射列の往復を同型へまとめる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def nerveFunctorFiberIso :
    nerve (Functor.Fiber p e) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (nerveMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex e) :=
  asIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorFiberMap p e)

/-- 概要：fiber の同型は元の全空間への包含を保つ。
方針：全次数での射列の往復を同型へまとめる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma nerveFunctorFiberIso_hom_inclusion : (nerveFunctorFiberIso p e).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (nerveMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex e) =
      nerveMap (Functor.Fiber.fiberInclusion (p := p) (S := e)) := rfl

/-- 概要：通常の関手の nerve の vertex fiber は quasicategory。
方針：通常の functor fiber の nerve との同型で内ホーン充填を移す。
規約：関手に isofibration 性を追加で要求しない。
使われ方：固定図式上の錐の族の同値の構成。 -/
instance nerveFunctorFiber_quasicategory :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (nerveMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex e)) :=
  quasicategory_of_innerFibration (nerveFunctorFiberIso p e).inv

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
