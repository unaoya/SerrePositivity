module
public import SerrePositivity.KST.SConstruction.AssemblyEdgeTriangle

/-! # 組み立てによる辺の三角形の三面
概要：内部の辺を対角へ写す三角形の三面を、対角・始点の object・零列へ同定する。
方針：区間積の三面、組み立ての次数変更、Yoneda の自然性を合成する。
規約：元の三角形を保持する。使われ方：対象 K 類の生成における辺の帰着。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 内部の辺と外側の区間を同じ向きに辿る元の組み立ての二単体。 -/
def assemblyEdgeTriangle (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (e : (X.obj (Opposite.op ⦋1⦌)) _⦋1⦌) :
    (Δ[2] : SSet.{u}) ⟶ simplicialDiagonalFunctor.obj X :=
  assemblyEdgeParameterTriangle ≫ ((Δ[1] : SSet.{u}) ◁ SSet.yonedaEquiv.symm e) ≫
    diagonalAssembly 1 X

/-- 三角形の第一面は元の対角の辺。 -/
lemma assemblyEdgeTriangle_face_one (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (e : (X.obj (Opposite.op ⦋1⦌)) _⦋1⦌) :
    stdSimplex.δ (1 : Fin 3) ≫ assemblyEdgeTriangle X e =
      (SSet.yonedaEquiv (X := simplicialDiagonalFunctor.obj X) (n := ⦋1⦌)).symm e := by
  rw [assemblyEdgeTriangle, ← Category.assoc, ← Category.assoc,
    assemblyEdgeParameterTriangle_face_one, lift_whiskerLeft]
  simp only [Category.id_comp]
  exact diagonalAssembly_diagonalSimplex X 1 e

/-- 内部の辺の始点での定数族は元の始点の頂点の定数射。 -/
lemma assemblyEdge_start_constant {Y : SSet.{u}} (e : Y _⦋1⦌) :
    SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
      (SSet.yonedaEquiv.symm e : (Δ[1] : SSet.{u}) ⟶ Y) =
        (SSet.const (Y.δ 1 e) : (Δ[1] : SSet.{u}) ⟶ Y) := by
  rw [SSet.const_comp]
  have h := stdSimplex.yonedaEquiv_δ_comp (SSet.yonedaEquiv.symm e) (1 : Fin 2)
  rw [stdSimplex.δ_one_eq_const, SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const,
    Equiv.apply_symm_apply] at h
  exact congrArg SSet.const h

/-- 三角形の第二面は元の内部始点の object の辺。 -/
lemma assemblyEdgeTriangle_face_two (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (e : (X.obj (Opposite.op ⦋1⦌)) _⦋1⦌) :
    stdSimplex.δ (2 : Fin 3) ≫ assemblyEdgeTriangle X e =
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const ((X.obj (Opposite.op ⦋1⦌)).δ 1 e)) ≫
        diagonalAssembly 1 X := by
  rw [assemblyEdgeTriangle, ← Category.assoc, ← Category.assoc,
    assemblyEdgeParameterTriangle_face_two, lift_whiskerLeft,
    assemblyEdge_start_constant]

/-- 三角形の第零面は、元の零列を潰す射の後では厳密に定数。 -/
lemma assemblyEdgeTriangle_face_zero {Y : SSet.{u}}
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (q : simplicialDiagonalFunctor.obj X ⟶ Y)
    (y : Y _⦋0⦌) (hq : diagonalZeroColumn X ≫ q = SSet.const y)
    (e : (X.obj (Opposite.op ⦋1⦌)) _⦋1⦌) :
    stdSimplex.δ (0 : Fin 3) ≫ assemblyEdgeTriangle X e ≫ q = SSet.const y := by
  let θ : ⦋0⦌ ⟶ ⦋1⦌ := SimplexCategory.const ⦋0⦌ ⦋1⦌ 1
  have hθ : lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (SSet.yonedaEquiv.symm e) =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (SSet.yonedaEquiv.symm e) ≫
      (stdSimplex.map θ ▷ X.obj (Opposite.op ⦋1⦌)) := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [assemblyEdgeTriangle, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    assemblyEdgeParameterTriangle_face_zero, Category.assoc, lift_whiskerLeft,
    Category.id_comp, hθ]
  simp only [Category.assoc]
  have ht : lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
      (SSet.yonedaEquiv.symm e) ≫
      ((stdSimplex.map θ ▷ X.obj (Opposite.op ⦋1⦌)) ≫ diagonalAssembly 1 X) ≫ q =
        SSet.const y := by
    rw [diagonalAssembly_endpoint 1 θ X]
    simp only [Category.assoc, hq, SSet.comp_const]
  simpa only [Category.assoc] using ht

end SerrePositivity.KST.SConstruction
