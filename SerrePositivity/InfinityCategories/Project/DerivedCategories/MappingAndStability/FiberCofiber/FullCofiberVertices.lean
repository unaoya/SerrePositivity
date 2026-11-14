module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FullCofiberSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed

/-! # 充満部分圏の標準 cofiber 正方形の頂点

概要：標準 cofiber 四角形の四頂点を所属証明付きの元の複体と同定する。
方針：上下の二単体の頂点を直接評価する。
規約：頂点の実際の等式。使われ方：D7 の明示的な suspension 四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] (P : _root_.SerrePositivity.DifferentialGraded.Complex S → Prop) {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (f : A ⟶ B) (g : A ⟶ C) (hA : P A) (hB : P B) (hC : P C)
variable (hP : P (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber f g))

/-- 標準 cofiber の始点は A。 -/
lemma fullCofiberSquare_vertex00 :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨A, hA⟩ : DGFullSubcategory (Complex S) P) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberUpperTriangle P f g hA hC hP) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _
  have hh := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 3))) h
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 0).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 3)) =
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2),
        SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply Prod.ext <;> decide
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app _ (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 3))) = _ at hh
  rw [hv] at hh
  apply hh.trans
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 標準 cofiber の右下の頂点は B。 -/
lemma fullCofiberSquare_vertex10 :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP) 1 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨B, hB⟩ : DGFullSubcategory (Complex S) P) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberLowerTriangle P f g hA hB hP) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _
  have hh := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3))) h
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 1).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3)) =
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply Prod.ext <;> decide
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1).app _ (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3))) = _ at hh
  rw [hv] at hh
  apply hh.trans
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 標準 cofiber の左上の頂点は C。 -/
lemma fullCofiberSquare_vertex01 :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP) 0 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨C, hC⟩ : DGFullSubcategory (Complex S) P) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberUpperTriangle P f g hA hC hP) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _
  have hh := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3))) h
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 0).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3)) =
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2),
        SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    apply Prod.ext <;> decide
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app _ (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3))) = _ at hh
  rw [hv] at hh
  apply hh.trans
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 標準 cofiber の終点は Q。 -/
lemma fullCofiberSquare_vertex11 :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP) 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber f g, hP⟩ : DGFullSubcategory (Complex S) P) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberUpperTriangle P f g hA hC hP) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _
  have hh := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (2 : Fin 3))) h
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 0).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    apply Prod.ext <;> decide
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app _ (SSet.stdSimplex.obj₀Equiv.symm (2 : Fin 3))) = _ at hh
  rw [hv] at hh
  apply hh.trans
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
