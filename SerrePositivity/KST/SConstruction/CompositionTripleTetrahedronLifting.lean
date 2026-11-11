module
public import SerrePositivity.KST.SConstruction.CompositionTripleHorns

/-! # 元の三面と指定全基底四面体を保つ両向きの結合替え
概要：fibration に沿い、元の全三合成面を保って指定全基底四面体を持ち上げる。
方針：同じ全内ホーンの後合成則と RLP を使い、得た全三単体を実合成表示へ戻す。
規約：基底の全三単体と出力全面を厳密に保持し、新たなモデル圏仮定を置かない。
使われ方：六結合替えの全選択を元の全高次 prism と同時に揃える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {E B : SSet.{u}} {w x y z : E _⦋0⦌}
  {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
  {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
  (first : SSet.Edge.CompStruct a b ab) (second : SSet.Edge.CompStruct b c bc)

/-- 元の全三面を保ち、指定全基底四面体と出力全面を同時に持ち上げる。 -/
def compositionTripleTetrahedronLiftData (right : SSet.Edge.CompStruct a bc abc)
    (p : E ⟶ B) [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron (first.map p) (second.map p) (right.map p)) :
    {V : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron first second right //
      SSet.yonedaEquiv.symm V.simplex ≫ p = SSet.yonedaEquiv.symm R.simplex ∧
      SSet.yonedaEquiv.symm V.left.simplex ≫ p = SSet.yonedaEquiv.symm R.left.simplex} := by
  let : HasLiftingProperty (horn 3 (1 : Fin 4)).ι p :=
    ((SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance) _ (horn_ι_mem_J 3 1)
  let sq : CommSq (compositionTripleHorn first second right) (horn 3 (1 : Fin 4)).ι p
      (SSet.yonedaEquiv.symm R.simplex) :=
    ⟨(compositionTripleHorn_post first second p right).trans
      (compositionTripleHorn_fac _ _ R).symm⟩
  let V := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleTetrahedronOfMap first second right sq.lift
    (by rw [← horn.ι_ι_assoc (1 : Fin 4) 0 (by decide), sq.fac_left,
      compositionTripleHorn_zero])
    (by rw [← horn.ι_ι_assoc (1 : Fin 4) 2 (by decide), sq.fac_left,
      compositionTripleHorn_two])
    (by rw [← horn.ι_ι_assoc (1 : Fin 4) 3 (by decide), sq.fac_left,
      compositionTripleHorn_three])
  have hp : SSet.yonedaEquiv.symm V.simplex ≫ p = SSet.yonedaEquiv.symm R.simplex := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv sq.lift) ≫ p = _
    rw [Equiv.symm_apply_apply]
    exact sq.fac_right
  refine ⟨V, hp, ?_⟩
  rw [V.left_face, R.left_face, ← stdSimplex.δ_comp_yonedaEquiv_symm,
    ← stdSimplex.δ_comp_yonedaEquiv_symm, Category.assoc, hp]

/-- 持ち上げた全四面体の射影は、指定した元の全基底四面体そのもの。 -/
lemma compositionTripleTetrahedronLiftData_projection
    (right : SSet.Edge.CompStruct a bc abc) (p : E ⟶ B) [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron (first.map p) (second.map p) (right.map p)) :
    SSet.yonedaEquiv.symm
        (compositionTripleTetrahedronLiftData first second right p R).val.simplex ≫ p =
      SSet.yonedaEquiv.symm R.simplex :=
  (compositionTripleTetrahedronLiftData first second right p R).property.1

/-- 出力した全面の射影も、同じ全基底四面体の残面そのもの。 -/
lemma compositionTripleTetrahedronLiftData_left
    (right : SSet.Edge.CompStruct a bc abc) (p : E ⟶ B) [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron (first.map p) (second.map p) (right.map p)) :
    SSet.yonedaEquiv.symm
        (compositionTripleTetrahedronLiftData first second right p R).val.left.simplex ≫ p =
      SSet.yonedaEquiv.symm R.left.simplex :=
  (compositionTripleTetrahedronLiftData first second right p R).property.2

/-- 元の全三面を保ち、指定全基底四面体と出力全面を同時に持ち上げる。 -/
def compositionTripleRightTetrahedronLiftData (left : SSet.Edge.CompStruct ab c abc)
    (p : E ⟶ B) [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron (first.map p) (second.map p) (left.map p)) :
    {V : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron first second left //
      SSet.yonedaEquiv.symm V.simplex ≫ p = SSet.yonedaEquiv.symm R.simplex ∧
      SSet.yonedaEquiv.symm V.right.simplex ≫ p = SSet.yonedaEquiv.symm R.right.simplex} := by
  let : HasLiftingProperty (horn 3 (2 : Fin 4)).ι p :=
    ((SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance) _ (horn_ι_mem_J 3 2)
  let sq : CommSq (compositionTripleRightHorn first second left) (horn 3 (2 : Fin 4)).ι p
      (SSet.yonedaEquiv.symm R.simplex) :=
    ⟨(compositionTripleRightHorn_post first second p left).trans
      (compositionTripleRightHorn_fac _ _ R).symm⟩
  let V := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleRightTetrahedronOfMap first second left sq.lift
    (by rw [← horn.ι_ι_assoc (2 : Fin 4) 0 (by decide), sq.fac_left,
      compositionTripleRightHorn_zero])
    (by rw [← horn.ι_ι_assoc (2 : Fin 4) 1 (by decide), sq.fac_left,
      compositionTripleRightHorn_one])
    (by rw [← horn.ι_ι_assoc (2 : Fin 4) 3 (by decide), sq.fac_left,
      compositionTripleRightHorn_three])
  have hp : SSet.yonedaEquiv.symm V.simplex ≫ p = SSet.yonedaEquiv.symm R.simplex := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv sq.lift) ≫ p = _
    rw [Equiv.symm_apply_apply]
    exact sq.fac_right
  refine ⟨V, hp, ?_⟩
  rw [V.right_face, R.right_face, ← stdSimplex.δ_comp_yonedaEquiv_symm,
    ← stdSimplex.δ_comp_yonedaEquiv_symm, Category.assoc, hp]

/-- 持ち上げた全四面体の射影は、指定した元の全基底四面体そのもの。 -/
lemma compositionTripleRightTetrahedronLiftData_projection
    (left : SSet.Edge.CompStruct ab c abc) (p : E ⟶ B) [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron (first.map p) (second.map p) (left.map p)) :
    SSet.yonedaEquiv.symm
        (compositionTripleRightTetrahedronLiftData first second left p R).val.simplex ≫ p =
      SSet.yonedaEquiv.symm R.simplex :=
  (compositionTripleRightTetrahedronLiftData first second left p R).property.1

/-- 出力した全面の射影も、同じ全基底四面体の残面そのもの。 -/
lemma compositionTripleRightTetrahedronLiftData_right
    (left : SSet.Edge.CompStruct ab c abc) (p : E ⟶ B) [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron (first.map p) (second.map p) (left.map p)) :
    SSet.yonedaEquiv.symm
        (compositionTripleRightTetrahedronLiftData first second left p R).val.right.simplex ≫ p =
      SSet.yonedaEquiv.symm R.right.simplex :=
  (compositionTripleRightTetrahedronLiftData first second left p R).property.2

/-- 出力した実合成面の全後合成像を、同じ元の基底合成面へ厳密に同定する。 -/
lemma compositionTripleTetrahedronLiftData_left_eq
    (right : SSet.Edge.CompStruct a bc abc) (p : E ⟶ B) [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron (first.map p) (second.map p) (right.map p)) :
    ((compositionTripleTetrahedronLiftData first second right p R).val.left).map p = R.left := by
  apply SSet.Edge.CompStruct.ext
  apply SSet.yonedaEquiv.symm.injective
  exact (SSet.yonedaEquiv_symm_comp _ _).symm.trans
    (compositionTripleTetrahedronLiftData_left first second right p R)

/-- 出力した実合成面の全後合成像を、同じ元の基底合成面へ厳密に同定する。 -/
lemma compositionTripleRightTetrahedronLiftData_right_eq
    (left : SSet.Edge.CompStruct ab c abc) (p : E ⟶ B) [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron (first.map p) (second.map p) (left.map p)) :
    ((compositionTripleRightTetrahedronLiftData first second left p R).val.right).map p =
      R.right := by
  apply SSet.Edge.CompStruct.ext
  apply SSet.yonedaEquiv.symm.injective
  exact (SSet.yonedaEquiv_symm_comp _ _).symm.trans
    (compositionTripleRightTetrahedronLiftData_right first second left p R)

end SerrePositivity.KST.SConstruction
