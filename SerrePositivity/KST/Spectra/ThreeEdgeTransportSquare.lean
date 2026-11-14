module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTrianglePushout
public import SerrePositivity.KST.Spectra.TriangleDiskFaces
public import SerrePositivity.KST.Spectra.FibrationEdgeComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ThreeEdgeTransport

/-!
概要：三辺輸送の二つの実三角形を同じ対角辺で貼り、四辺を保持する実正方形を作る。
方針：元の first・second の二単体を正方形の pushout へそのまま降ろす。
規約：Kan 性の追加仮定なし。使われ方：段調整と相対修正の正方形の共通辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.ThreeEdgeTransport
variable {E : SSet.{u}} {x a y b : E _⦋0⦌}
  {left : E.Edge x a} {middle : E.Edge x y} {right : E.Edge y b}
  (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right)

/-- 保存した二つの実三角形を、同じ対角辺で貼った実正方形。 -/
def square : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.desc (SSet.yonedaEquiv.symm D.first.simplex)
    (SSet.yonedaEquiv.symm D.second.simplex) (by
      rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
        SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm])

/-- 上側の二単体は、元の第一の輸送三角形単体そのもの。 -/
@[reassoc (attr := simp)]
lemma square_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ square D = SSet.yonedaEquiv.symm D.first.simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.inl_desc _ _ _

/-- 下側の二単体は、元の第二の輸送三角形単体そのもの。 -/
@[reassoc (attr := simp)]
lemma square_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ square D =
      SSet.yonedaEquiv.symm D.second.simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.inr_desc _ _ _

/-- 正方形の始辺は、元の左辺そのもの。 -/
lemma square_zero :
    SSet.ι₀ ≫ square D = SSet.yonedaEquiv.symm left.edge := by
  have h : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ _) =
      lift (𝟙 _) (stdSimplex.isTerminalObj₀.from _) ≫
        (Δ[1] : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 2) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  rw [h, Category.assoc, SquareTriangles.second_endpoint_one, Category.assoc,
    Category.assoc, square_lower,
    SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm, ← Category.assoc, lift_fst,
    Category.id_comp]

/-- 正方形の終辺は、元の右辺そのもの。 -/
lemma square_one :
    SSet.ι₁ ≫ square D = SSet.yonedaEquiv.symm right.edge := by
  have h : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ _) =
      lift (𝟙 _) (stdSimplex.isTerminalObj₀.from _) ≫
        (Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  rw [h, Category.assoc, SquareTriangles.second_endpoint_zero, Category.assoc,
    Category.assoc, square_upper,
    SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm, ← Category.assoc, lift_fst,
    Category.id_comp]

/-- 始点を動かす辺は、元の中央辺をそのまま保持する。 -/
lemma square_start :
    stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ square D =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm middle.edge := by
  rw [SquareTriangles.first_endpoint_one, Category.assoc, Category.assoc,
    square_upper, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]

/-- 終点を動かす辺は、選んだ元の輸送辺そのもの。 -/
lemma square_finish :
    stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ square D =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm D.transported.edge := by
  rw [SquareTriangles.first_endpoint_zero, Category.assoc, Category.assoc,
    square_lower, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]

/-- 左辺から右辺への、元の中央辺と輸送辺を境界に持つ実ホモトピー。 -/
def homotopy : SSet.Homotopy (SSet.yonedaEquiv.symm left.edge)
    (SSet.yonedaEquiv.symm right.edge) where
  h := square D
  h₀ := square_zero D
  h₁ := square_one D
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

end SerrePositivity.KST.Spectra.ThreeEdgeTransport
