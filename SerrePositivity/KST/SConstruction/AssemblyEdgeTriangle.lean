module
public import SerrePositivity.KST.SConstruction.ObjectAssemblySimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans

/-! # 対角の辺と内部の頂点の辺を結ぶ組み立ての三角形
概要：区間の積の三角形と対角組み立てを照合する。
方針：標準単体の二つの退化写像の積を用い、三つの面を厳密に計算する。
規約：外側・内側の区間を同時に同じ向きへ辿る。使われ方：K の対象類による辺の生成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 外側の単体と同じ内部の単体を組み立てると、元の対角単体を回収する。 -/
lemma diagonalAssembly_diagonalSimplex (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    (s : (X.obj (Opposite.op ⦋n⦌)) _⦋n⦌) :
    lift (𝟙 (Δ[n] : SSet.{u})) (SSet.yonedaEquiv.symm s) ≫ diagonalAssembly n X =
      (SSet.yonedaEquiv (X := simplicialDiagonalFunctor.obj X) (n := ⦋n⦌)).symm s := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro a
  exact ConcreteCategory.congr_hom
    ((X.map (stdSimplex.objEquiv a).op).naturality (stdSimplex.objEquiv a).op) s

/-- 区間の積の下辺・右辺・対角を持つ、元の二単体。 -/
def assemblyEdgeParameterTriangle : (Δ[2] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] :=
  lift (stdSimplex.σ (1 : Fin 2)) (stdSimplex.σ (0 : Fin 2))

/-- パラメータ三角形の第零面は右辺。 -/
lemma assemblyEdgeParameterTriangle_face_zero :
    stdSimplex.δ (0 : Fin 3) ≫ assemblyEdgeParameterTriangle.{u} =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
        (𝟙 (Δ[1] : SSet.{u})) := by
  apply NatTrans.ext
  funext ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Prod.ext <;> apply stdSimplex.ext <;> intro j
  · change (SimplexCategory.σ (1 : Fin 2)).toOrderHom
      ((SimplexCategory.δ (0 : Fin 3)).toOrderHom (a j)) = 1
    generalize a j = k
    fin_cases k <;> rfl
  · change (SimplexCategory.σ (0 : Fin 2)).toOrderHom
      ((SimplexCategory.δ (0 : Fin 3)).toOrderHom (a j)) = a j
    generalize a j = k
    fin_cases k <;> rfl

/-- パラメータ三角形の第一面は対角。 -/
lemma assemblyEdgeParameterTriangle_face_one :
    stdSimplex.δ (1 : Fin 3) ≫ assemblyEdgeParameterTriangle.{u} =
      lift (𝟙 (Δ[1] : SSet.{u})) (𝟙 (Δ[1] : SSet.{u})) := by
  apply NatTrans.ext
  funext ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Prod.ext <;> apply stdSimplex.ext <;> intro j
  · change (SimplexCategory.σ (1 : Fin 2)).toOrderHom
      ((SimplexCategory.δ (1 : Fin 3)).toOrderHom (a j)) = a j
    generalize a j = k
    fin_cases k <;> rfl
  · change (SimplexCategory.σ (0 : Fin 2)).toOrderHom
      ((SimplexCategory.δ (1 : Fin 3)).toOrderHom (a j)) = a j
    generalize a j = k
    fin_cases k <;> rfl

/-- パラメータ三角形の第二面は下辺。 -/
lemma assemblyEdgeParameterTriangle_face_two :
    stdSimplex.δ (2 : Fin 3) ≫ assemblyEdgeParameterTriangle.{u} =
      lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  apply NatTrans.ext
  funext ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Prod.ext <;> apply stdSimplex.ext <;> intro j
  · change (SimplexCategory.σ (1 : Fin 2)).toOrderHom
      ((SimplexCategory.δ (2 : Fin 3)).toOrderHom (a j)) = a j
    generalize a j = k
    fin_cases k <;> rfl
  · change (SimplexCategory.σ (0 : Fin 2)).toOrderHom
      ((SimplexCategory.δ (2 : Fin 3)).toOrderHom (a j)) = 0
    generalize a j = k
    fin_cases k <;> rfl

end SerrePositivity.KST.SConstruction
