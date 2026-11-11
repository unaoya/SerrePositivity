module
public import SerrePositivity.KST.SConstruction.CoherentStringDiagramCells
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

/-! # strict 図式の元の Path 評価は定数族
概要：元の strict 図式の全高次 Path 評価が、元の水平射の定数単体であることを証明する。
方針：通常の順序図式の豊穣表示を計算し、元の写像と全次数を保持する。
規約：局所 Kan 性も新たな高次充填も要求しない。
使われ方：上下の K prism の水平部分を元の段の写像へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- strict 図式の全 Path 作用は、同じ元の水平射に値を取る定数族。 -/
lemma coherentStringDiagramCell_strict_map {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : I ⥤ C)
    {n : ℕ} (s : (nerve I) _⦋n⦌) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (coherentStringDiagramCell (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) s).map (.mk (ULift.up i))
      (.mk (ULift.up j)) =
      SSet.const (SimplicialCategory.homEquiv' _ _ (F.map (s.map (homOfLE hij)))) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
    (F.map (s.map (homOfLE (show i ≤ j from SimplicialThickening.Path.le (J := ULift.{u} (Fin (n + 1))) (P.obj 0)))))) d = _
  rfl

end SerrePositivity.KST.SConstruction
