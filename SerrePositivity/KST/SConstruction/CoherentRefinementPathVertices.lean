module
public import SerrePositivity.KST.SConstruction.CoherentArrowNativeFamilies

/-! # 元の全頂点 Path の精密化による厳密な回収
概要：元の合成列の全頂点 Path の像が、元の精密化の Path そのものであることを証明する。
方針：精密化の合成則と native Hom 評価の自然性を頂点で用いる。
規約：元の Path と元の豊穣作用を保持する。
使われ方：全パラメータの終点族の定数値を、元の短い二合成の値へ回収する。
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
variable {I : Type u} [SmallCategory I] {x y : I} {f : x ⟶ y}

/-- 元の全頂点 Path の精密化による像は、元の精密化の像の Path そのもの。 -/
lemma coherentStringPathReindex_fullPath {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f} (a : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathReindex a (coherentStringFullPath s) = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath a := by
  simpa only [Category.id_comp, coherentStringRefinementPath_id] using
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath_comp (𝟙 s) a).symm

/-- 精密化の像の Path の値は、元の列の全頂点 Path の値を厳密に回収する。 -/
lemma coherentStringNativeMap_refinementVertex
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f} (a : s ⟶ t) :
    (coherentStringNativeMap Q t).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath a)) =
      (coherentStringNativeMap Q s).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath s)) := by
  have hv : (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathReindexFunctor a)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath s)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath a) := by
    apply ComposableArrows.ext₀
    exact coherentStringPathReindex_fullPath a
  have h := congrArg (fun k => k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath s)))
    (coherentStringNativeMap_naturality Q a)
  change (coherentStringNativeMap Q t).app _
    ((nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathReindexFunctor a)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath s))) = _ at h
  rw [hv] at h
  exact h

end SerrePositivity.KST.SConstruction
