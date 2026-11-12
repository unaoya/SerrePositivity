module
public import SerrePositivity.KST.SConstruction.CoherentHomotopyPrisms

/-! # 合成二単体の prism の元の三つの三単体
概要：二単体と区間の積の三つの階段状三単体と、その共有面・元の四角形の面を指定する。
方針：元の水平座標と時刻座標を有限順序写像として保つ。
規約：元の積の単体そのものを使い、Kan の充填を選ばない。
使われ方：元の入力の合成 prism からの三つの実 Hom 正方形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 三つの階段状三単体の、元の二単体への水平座標。 -/
def trianglePrismHorizontal (q : Fin 3) : ⦋3⦌ ⟶ ⦋2⦌ :=
  SimplexCategory.mkHom ⟨![![0, 0, 1, 2], ![0, 1, 1, 2], ![0, 1, 2, 2]] q,
    by fin_cases q <;> decide⟩

/-- 三つの階段状三単体の、元の区間への時刻座標。 -/
def trianglePrismTime (q : Fin 3) : ⦋3⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom ⟨![![0, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]] q,
    by fin_cases q <;> decide⟩

/-- 元の二単体 prism の三つの三単体。 -/
def trianglePrismTetrahedron (q : Fin 3) : ((Δ[2] : SSet.{u}) ⊗ Δ[1]) _⦋3⦌ :=
  (SSet.stdSimplex.objEquiv.symm (trianglePrismHorizontal q),
    SSet.stdSimplex.objEquiv.symm (trianglePrismTime q))

/-- 元の二単体の最初・最後・合成の三辺の包含。 -/
def trianglePrismEdge (e : Fin 3) : ⦋1⦌ ⟶ ⦋2⦌ :=
  ![SimplexCategory.δ (2 : Fin 3), SimplexCategory.δ (0 : Fin 3),
    SimplexCategory.δ (1 : Fin 3)] e

/-- 指定した元の辺の四角形の上側三角形。 -/
def trianglePrismUpper (e : Fin 3) : ((Δ[2] : SSet.{u}) ⊗ Δ[1]) _⦋2⦌ :=
  (SSet.stdSimplex.map (trianglePrismEdge e) ▷ (Δ[1] : SSet.{u})).app _
    (((SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
      (SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).simplex)

/-- 指定した元の辺の四角形の下側三角形。 -/
def trianglePrismLower (e : Fin 3) : ((Δ[2] : SSet.{u}) ⊗ Δ[1]) _⦋2⦌ :=
  (SSet.stdSimplex.map (trianglePrismEdge e) ▷ (Δ[1] : SSet.{u})).app _
    (((SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
      (SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).simplex)

/-- 最初と中央の三単体は、同じ元の内側三角形を共有する。 -/
lemma trianglePrismTetrahedron_shared_first :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 1 (trianglePrismTetrahedron 0) =
      ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 1 (trianglePrismTetrahedron 1) := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 中央と最後の三単体も、同じ元の内側三角形を共有する。 -/
lemma trianglePrismTetrahedron_shared_second :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 2 (trianglePrismTetrahedron 1) =
      ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 2 (trianglePrismTetrahedron 2) := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 最初の三単体の二番面は、元の合成辺の上側三角形。 -/
lemma trianglePrismTetrahedron_composite_upper :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 2 (trianglePrismTetrahedron 0) = trianglePrismUpper 2 := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 最後の三単体の一番面は、元の合成辺の下側三角形。 -/
lemma trianglePrismTetrahedron_composite_lower :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 1 (trianglePrismTetrahedron 2) = trianglePrismLower 2 := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 最初の三単体の三番面は、元の前の辺の上側三角形。 -/
lemma trianglePrismTetrahedron_first_upper :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 3 (trianglePrismTetrahedron 0) = trianglePrismUpper 0 := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 中央の三単体の三番面は、元の前の辺の下側三角形。 -/
lemma trianglePrismTetrahedron_first_lower :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 3 (trianglePrismTetrahedron 1) = trianglePrismLower 0 := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 中央の三単体の零番面は、元の後ろの辺の上側三角形。 -/
lemma trianglePrismTetrahedron_second_upper :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 0 (trianglePrismTetrahedron 1) = trianglePrismUpper 1 := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 最後の三単体の零番面は、元の後ろの辺の下側三角形。 -/
lemma trianglePrismTetrahedron_second_lower :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 0 (trianglePrismTetrahedron 2) = trianglePrismLower 1 := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 最初の三単体の零番面は、元の二単体の上面そのもの。 -/
lemma trianglePrismTetrahedron_top :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 0 (trianglePrismTetrahedron 0) =
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋2⦌),
        SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋2⦌ ⦋1⦌ 1)) := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 最後の三単体の三番面は、元の二単体の下面そのもの。 -/
lemma trianglePrismTetrahedron_bottom :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]).δ 3 (trianglePrismTetrahedron 2) =
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋2⦌),
        SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋2⦌ ⦋1⦌ 0)) := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

end SerrePositivity.KST.SConstruction
