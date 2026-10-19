module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblySelectedNaturality
public import SerrePositivity.KST.SConstruction.ContractiblePathComparison

/-! # 自然性パラメーターの指定した辺の評価
概要：指定したパラメーター辺を自然性の辺へ移し、異なる辺の像を比較する。
方針：両端の厳密な回収と可縮パラメーターの三角形を使う。
規約：入力するパラメーター辺を選び直さない。
使われ方：円筒の具体的な辺列と選択済みの自然性ホモトピーの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 指定した自然性パラメーターの辺を実際の写像空間の辺へ移す。 -/
def boundaryAssemblyNaturalityEdgeAt (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (e : (boundaryAssemblyNaturalityParameters r f).Edge
      ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v)
      ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w)) :
    (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
      ((loopBoundaryKanFunctor (r + 1)).obj Y)).right.Edge
      (familyVertex (boundaryKanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f))
      (familyVertex ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjointAt r Y w)) :=
  (e.map (boundaryAssemblyNaturalityFamilyAt r f u)).ofEq
    (boundaryAssemblyNaturalityFamilyAt_source_vertex r f u v)
    (boundaryAssemblyNaturalityFamilyAt_target_vertex r f u w)

/-- 同じ両端の任意の指定したパラメーター辺の評価はホモトピー圏で一致する。 -/
lemma boundaryAssemblyNaturalityEdgeAt_parallel (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (e e' : (boundaryAssemblyNaturalityParameters r f).Edge
      ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v)
      ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w)) :
    SSet.HomotopyCategory.homMk (boundaryAssemblyNaturalityEdgeAt r f u v w e) =
      SSet.HomotopyCategory.homMk (boundaryAssemblyNaturalityEdgeAt r f u v w e') := by
  let F := boundaryAssemblyNaturalityFamilyAt r f u
  let p := (boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w
  let z := familyVertex ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjointAt r Y w)
  have hi : ((SSet.Edge.id p).map F).edge = (SSet.Edge.id z).edge := by
    rw [SSet.Edge.map_id, SSet.Edge.id_edge, SSet.Edge.id_edge]
    exact congrArg _ (boundaryAssemblyNaturalityFamilyAt_target_vertex r f u w)
  obtain ⟨h⟩ := contractibleKan_mapped_compStruct
    (boundaryAssemblyNaturalityParameters_isContractibleKan r f) F e (.id p) e'
    (boundaryAssemblyNaturalityEdgeAt r f u v w e) (.id z)
    (boundaryAssemblyNaturalityEdgeAt r f u v w e') rfl hi rfl
  have hh := SSet.HomotopyCategory.homMk_comp_homMk h
  have hhid := SSet.HomotopyCategory.homMk_id z
  rw [hhid, Category.comp_id] at hh
  exact hh

end SerrePositivity.KST.SConstruction
