module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CoherentStringPathFlags
public import SerrePositivity.KST.SConstruction.CoherentArrowStringInitial
public import SerrePositivity.KST.SConstruction.CoherentSimplexArrows

/-! # 合成列の全頂点 Path と元の長辺の回収
概要：精密化パラメータの各頂点と初点で、全頂点 Path と元の二端点 Path を回収する。
方針：恒等再添字の像と標準端点射の像を元の有限集合として比較する。
規約：長さ零の列と元の射そのものの列を保持する。
使われ方：native Hom の全合成列族が元の長辺から始まることを厳密に照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {x y : I} {f : x ⟶ y}

/-- 元の合成列の全頂点を含む Path。 -/
def coherentStringFullPath (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    Path (ULift.up 0 : ULift.{u} (Fin (s.length + 1))) (ULift.up (Fin.last s.length)) where
  I := Set.univ
  left := Set.mem_univ _
  right := Set.mem_univ _
  left_le _ _ := Fin.zero_le _
  le_right _ _ := Fin.le_last _

/-- 恒等精密化の Path は元の合成列の全頂点 Path そのもの。 -/
lemma coherentStringRefinementPath_id (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath (𝟙 s) = coherentStringFullPath s := by
  apply SimplicialThickening.Path.ext
  ext q
  change (∃ i, ULift.up i = q) ↔ True
  exact ⟨fun _ => trivial, fun _ => ⟨q.down, rfl⟩⟩

/-- 元の射から全合成列への標準精密化の像は、同じ元の二端点だけの Path。 -/
lemma coherentStringRefinementPath_directTo (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath (coherentArrowStringDirectTo s) =
      coherentEndpointPath (show (ULift.up 0 : ULift.{u} (Fin (s.length + 1))) ≤
        ULift.up (Fin.last s.length) from Fin.zero_le _) := by
  apply SimplicialThickening.Path.ext
  ext q
  change (∃ i : Fin 2, ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap s.length).toOrderHom i) = q) ↔
    q = ULift.up 0 ∨ q = ULift.up (Fin.last s.length)
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl ((congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_first _)).symm.trans hi).symm
    · exact Or.inr ((congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_last _)).symm.trans hi).symm
  · rintro (rfl | rfl)
    · exact ⟨0, congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_first _)⟩
    · exact ⟨1, congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_last _)⟩

/-- 高次 Path 族の元の合成列の頂点では、同じ全頂点 Path を厳密に回収する。 -/
lemma coherentStringPathFlag_vertex (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath s) := by
  apply ComposableArrows.ext₀
  exact coherentStringRefinementPath_id s

/-- 元の射だけの合成列では、全頂点 Path は元の二端点 Path そのもの。 -/
lemma coherentStringFullPath_direct (f : x ⟶ y) :
    coherentStringFullPath (coherentArrowStringDirect f) =
      coherentEndpointPath (show (ULift.up 0 : ULift.{u} (Fin 2)) ≤ ULift.up 1 from by decide) := by
  exact (coherentStringRefinementPath_id _).symm.trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath
      (coherentArrowStringDirectTo_unique _ (𝟙 (coherentArrowStringDirect f)))).trans
        (coherentStringRefinementPath_directTo _))

end SerrePositivity.KST.SConstruction
