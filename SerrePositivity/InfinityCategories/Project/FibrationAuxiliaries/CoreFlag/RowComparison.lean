module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.TransposeSimplex
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.Rows

/-!
概要：core 旗を転置した行と全辺可逆な図式の部分圏の比較。
方針：二つの標準単体の変数を交換し、点ごとの可逆性判定で core 条件を移す。
規約：評価を外側次数について自然と主張しない。
使われ方：Sp-8 の定数二重単体集合からの行弱同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag
open _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories

/-- パラメーター次数を外側にした core 旗。 -/
def transposeResolution (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.resolution C).flip

/-- 転置した各行は全辺可逆な標準単体図式の部分圏。 -/
def rowIso (C : SSet.{u}) [Quasicategory C] (m : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeResolution C).obj m ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceDiagrams (stdSimplex.obj m.unop) C where
  hom :=
    { app n := ↾fun s ↦ ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex s.val, (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transpose_mem_iff s.val).mp s.property⟩
      naturality {n k} f := by
        apply ConcreteCategory.hom_ext
        intro s
        apply Subtype.ext
        apply Functor.functorHom_ext
        intro d g
        apply ConcreteCategory.hom_ext
        intro x
        dsimp [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeResolution, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.resolution, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.functorDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceDiagrams,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex]
        change s.val.app d ((𝟙 m) ≫ (stdSimplex.objEquiv x).op)
            ((stdSimplex.map f.unop).app d (stdSimplex.objEquiv.symm g.unop)) =
          s.val.app d (stdSimplex.objEquiv x).op (stdSimplex.objEquiv.symm (f ≫ g).unop)
        simp only [Category.id_comp]
        congr 1 }
  inv :=
    { app n := ↾fun s ↦ ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex s.val, (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transpose_mem_iff _).mpr (by
        rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex_transposeSimplex]
        exact s.property)⟩
      naturality {n k} f := by
        apply ConcreteCategory.hom_ext
        intro s
        apply Subtype.ext
        apply Functor.functorHom_ext
        intro d g
        apply ConcreteCategory.hom_ext
        intro x
        dsimp [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeResolution, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.resolution, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.functorDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceDiagrams,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex]
        change s.val.app d (f ≫ (stdSimplex.objEquiv x).op) (stdSimplex.objEquiv.symm g.unop) =
          s.val.app d (stdSimplex.objEquiv ((stdSimplex.map f.unop).app d x)).op
            (stdSimplex.objEquiv.symm ((𝟙 m) ≫ g).unop)
        simp only [Category.id_comp]
        congr 2 }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex_transposeSimplex s.val
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex_transposeSimplex s.val

/-- パラメーター方向に定値な二重単体集合。 -/
def constantDiagram (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj C

/-- 元の旗を保持する行定数包含。 -/
def rowInclusion (C : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    C ⟶ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeResolution C).obj m where
  app n := ↾fun s ↦ ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.constantSimplex s, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.constantSimplex_mem s⟩
  naturality {n k} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Functor.functorHom_ext
    intro d g
    apply ConcreteCategory.hom_ext
    intro x
    change C.map (stdSimplex.objEquiv x).op (C.map f s) =
      C.map (stdSimplex.objEquiv ((stdSimplex.map f.unop).app d x)).op s
    have hc := C.map_comp_apply f (stdSimplex.objEquiv x).op s
    dsimp at hc ⊢
    rw [← hc]
    congr 2

/-- 各行の定数包含を二重単体集合の射として束ねる。 -/
def bisimplicialInclusion (C : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.constantDiagram C ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeResolution C where
  app m := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.rowInclusion C m
  naturality {m k} f := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl

/-- 行の同定は元の定数包含を通常の定値図式に送る。 -/
lemma rowInclusion_rowIso (C : SSet.{u}) [Quasicategory C] (m : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.rowInclusion C m ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.rowIso C m).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.constant (stdSimplex.obj m.unop) C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Functor.functorHom_ext
  intro d g
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 転置した全行の定数包含は弱ホモトピー同値。 -/
lemma rowInclusion_isWeakHomotopyEquivalence (C : SSet.{u}) [Quasicategory C]
    (m : SimplexCategoryᵒᵖ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.rowInclusion C m) := by
  have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.rowIso C m)).isWeakHomotopyEquivalence
  apply hm.cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.rowInclusion_rowIso]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.simplexConstant_isWeakHomotopyEquivalence C m.unop.len

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
