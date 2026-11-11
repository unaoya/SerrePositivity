module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorNaturalitySquare
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square

/-!
概要：自然性の四角形を、同じ長辺を持つ二つの三角形の族に分ける。
方針：標準正方形の二つの三角形で制限し、四辺と共通対角を厳密に計算する。
規約：三角形を別々に充填せず、元の四角形と全パラメーターを保つ。
使われ方：coherent な自然性の二つの合成順序を同じ長辺で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 零番三角形の最初の辺は四角形の第一座標を零に固定する。 -/
lemma squareTriangle_zero_initialFace :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 零番三角形の最後の辺は第二座標を一に固定する。 -/
lemma squareTriangle_zero_finalFace :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 =
      lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 一番三角形の最初の辺は第二座標を零に固定する。 -/
lemma squareTriangle_one_initialFace :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 =
      lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 一番三角形の最後の辺は第一座標を一に固定する。 -/
lemma squareTriangle_one_finalFace :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 四角形の族を、その二つの標準三角形の一方へ制限する。 -/
def squarePrismTriangle {P Y : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Y) (i : Fin 2) : Δ[2] ⊗ P ⟶ Y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i ▷ P) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] P).hom ≫ R

/-- 零番三角形の最初の辺は、変換の零端での四角形の辺。 -/
lemma squarePrismTriangle_zero_initial {P Y : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Y) :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ squarePrismTriangle R 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ P) ≫ R := by
  rw [squarePrismTriangle, ← Category.assoc, ← comp_whiskerRight,
    squareTriangle_zero_initialFace]
  rfl

/-- 零番三角形の最後の辺は、射の一端での四角形の辺。 -/
lemma squarePrismTriangle_zero_final {P Y : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Y) :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ squarePrismTriangle R 0 =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P) ≫ R := by
  rw [squarePrismTriangle, ← Category.assoc, ← comp_whiskerRight,
    squareTriangle_zero_finalFace]
  rfl

/-- 一番三角形の最初の辺は、射の零端での四角形の辺。 -/
lemma squarePrismTriangle_one_initial {P Y : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Y) :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ squarePrismTriangle R 1 =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P) ≫ R := by
  rw [squarePrismTriangle, ← Category.assoc, ← comp_whiskerRight,
    squareTriangle_one_initialFace]
  rfl

/-- 一番三角形の最後の辺は、変換の一端での四角形の辺。 -/
lemma squarePrismTriangle_one_final {P Y : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Y) :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ squarePrismTriangle R 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ P) ≫ R := by
  rw [squarePrismTriangle, ← Category.assoc, ← comp_whiskerRight,
    squareTriangle_one_finalFace]
  rfl

/-- どちらの三角形の長辺も、元の四角形の同じ対角の族そのもの。 -/
lemma squarePrismTriangle_diagonal {P Y : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Y) (i : Fin 2) :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ squarePrismTriangle R i =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ▷ P) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] P).hom ≫ R := by
  rw [squarePrismTriangle, ← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]

/-- 三角形への制限は任意のパラメーター制限と可換。 -/
lemma squarePrismTriangle_restrict {P Q Y : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Y) (k : Q ⟶ P) (i : Fin 2) :
    (Δ[2] ◁ k) ≫ squarePrismTriangle R i =
      squarePrismTriangle ((Δ[1] ◁ (Δ[1] ◁ k)) ≫ R) i := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, p⟩
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
