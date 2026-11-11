module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.TriangleBoundaryGluing
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathMap

/-!
概要：三角形の二辺を固定し、対角辺だけを可逆 path に沿って動かす境界図式。
方針：ホーン上には定値 path を置き、対角辺上の指定 path と二端点で貼り合わせる。
規約：対角辺の path 自体を保持し、始点の境界を厳密に回収する。
使われ方：基準合成三角形を導来 fiber の path に沿って運ぶための境界データ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：二辺を固定して対角辺を動かす三角形の境界上の可逆 path の図式。
方針：二辺のホーンの定値 path と指定対角辺の path を貼り合わせる。
規約：二端点の厳密な一致を入力として保持する。
使われ方：関手図式の相対 path 持ち上げへの入力。 -/
noncomputable def triangleBoundaryPath {Z : SSet.{u}}
    (T : (Δ[2] : SSet.{u}) ⟶ Z) (p : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Z)
    (h₀ : stdSimplex.δ (1 : Fin 2) ≫ p =
      stdSimplex.δ (1 : Fin 2) ≫ horn₂₁.ι₀₁ ≫ (horn 2 1).ι ≫ T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Z)
    (h₂ : stdSimplex.δ (0 : Fin 2) ≫ p =
      stdSimplex.δ (0 : Fin 2) ≫ horn₂₁.ι₁₂ ≫ (horn 2 1).ι ≫ T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Z) :
    (boundary 2 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Z :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryDiagram ((horn 2 1).ι ≫ T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Z) p
    (by simpa only [Category.assoc] using h₀)
    (by simpa only [Category.assoc] using h₂)

/-- 概要：境界の path の第 1 面は指定された対角辺の path そのもの。
方針：境界図式の対角辺の制限公式。
規約：ホモトピー類だけでなく実際の path を保持する。
使われ方：逆向きの比較で導来 fiber の path を回収する。 -/
lemma triangleBoundaryPath_face_one {Z : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ Z)
    (p : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Z) (h₀) (h₂) :
    boundary.ι (1 : Fin 3) ≫ triangleBoundaryPath T p h₀ h₂ = p :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryDiagram_face_one _ _ _ _

/-- 概要：境界の path の第 2 面は基準三角形の前辺における定値 path。
方針：ホーンの前辺への制限とホーンの包含公式。
規約：前辺は厳密に固定する。
使われ方：単位の代表を保持する。 -/
lemma triangleBoundaryPath_face_two {Z : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ Z)
    (p : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Z) (h₀) (h₂) :
    boundary.ι (2 : Fin 3) ≫ triangleBoundaryPath T p h₀ h₂ =
      stdSimplex.δ (2 : Fin 3) ≫ T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Z := by
  unfold triangleBoundaryPath
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryDiagram_face_two]
  change horn.ι 1 (2 : Fin 3) (by decide) ≫ (horn 2 1).ι ≫ T ≫ _ = _
  rw [reassoc_of% horn.ι_ι]

/-- 概要：境界の path の第 0 面は基準三角形の後辺における定値 path。
方針：ホーンの後辺への制限とホーンの包含公式。
規約：後辺は厳密に固定する。
使われ方：G による標的辺を保持する。 -/
lemma triangleBoundaryPath_face_zero {Z : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ Z)
    (p : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Z) (h₀) (h₂) :
    boundary.ι (0 : Fin 3) ≫ triangleBoundaryPath T p h₀ h₂ =
      stdSimplex.δ (0 : Fin 3) ≫ T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Z := by
  unfold triangleBoundaryPath
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryDiagram_face_zero]
  change horn.ι 1 (0 : Fin 3) (by decide) ≫ (horn 2 1).ι ≫ T ≫ _ = _
  rw [reassoc_of% horn.ι_ι]

/-- 概要：対角辺の path が基準対角辺から始まれば、貼り合わせた境界の始点は基準境界。
方針：境界の三面で検査し、固定二辺と対角辺の始点を計算する。
規約：始点の等式は厳密。
使われ方：相対 path の持ち上げで指定する始点の図式。 -/
lemma triangleBoundaryPath_start {Z : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ Z)
    (p : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Z) (h₀) (h₂)
    (hp : p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Z 0 = stdSimplex.δ (1 : Fin 3) ≫ T) :
    triangleBoundaryPath T p h₀ h₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Z 0 = (boundary 2).ι ≫ T := by
  apply boundary.hom_ext
  intro i
  fin_cases i
  · rw [← Category.assoc]
    change (boundary.ι (0 : Fin 3) ≫ triangleBoundaryPath T p h₀ h₂) ≫ _ = _
    rw [triangleBoundaryPath_face_zero]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id,
      reassoc_of% boundary.ι_ι]
    rfl
  · rw [← Category.assoc]
    change (boundary.ι (1 : Fin 3) ≫ triangleBoundaryPath T p h₀ h₂) ≫ _ = _
    rw [triangleBoundaryPath_face_one, hp, ← Category.assoc, boundary.ι_ι]
    rfl
  · rw [← Category.assoc]
    change (boundary.ι (2 : Fin 3) ≫ triangleBoundaryPath T p h₀ h₂) ≫ _ = _
    rw [triangleBoundaryPath_face_two]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id,
      reassoc_of% boundary.ι_ι]
    rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
