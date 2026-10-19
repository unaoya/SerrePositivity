module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyFactorization

/-! # 指定した自然性のパラメーターと評価のデータ
概要：因子辺・自然性の辺・評価延長を独立に指定する。
方針：可縮な選択空間の入力を一つのデータへ束ねる。
規約：データを束ねる際に選択を変更しない。
使われ方：複数の入力の自然性の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 自然性の辺と二つの因子辺、評価族の延長を全て指定したデータ。 -/
structure BoundaryAssemblyNaturalityData (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌) where
  extension : (kanAssemblyMixedChoices r f).Edge
    ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v.2)
    ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.2)
  inverse : (oneDirectionInverseMixedChoices r f).Edge
    ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v.1)
    ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w.1)
  parameter : (boundaryAssemblyNaturalityParameters r f).Edge
    ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v)
    ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w)
  evaluation : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌

/-- 任意の両端の構造射選択について、全ての自然性データを指定できる。 -/
lemma boundaryAssemblyNaturalityData_nonempty (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌) :
    Nonempty (BoundaryAssemblyNaturalityData r f v w) := by
  obtain ⟨a⟩ := kanAssemblyMixedChoices_nonempty_edge r f v.2 w.2
  obtain ⟨b⟩ := oneDirectionInverseMixedChoices_nonempty_edge r f v.1 w.1
  obtain ⟨p⟩ := ((boundaryAssemblyNaturalityParameters_isContractibleKan r f).isTerminalVertex
    ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w)).nonempty_edge
      ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v)
  obtain ⟨z⟩ := (boundaryAssemblyNaturalityFamilyChoices_isContractibleKan r f).nonempty
  exact ⟨⟨a, b, SSet.Edge.ofTruncated p, z⟩⟩

/-- 指定した全てのデータで評価した元の構造射の自然性の辺。 -/
def boundaryAssemblyChosenNaturalityEdge (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (d : BoundaryAssemblyNaturalityData r f v w) :
    (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
      ((loopBoundaryKanFunctor (r + 1)).obj Y)).right.Edge
      (familyVertex (boundaryKanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f))
      (familyVertex ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjointAt r Y w)) :=
  boundaryAssemblyNaturalityEdgeAt r f d.evaluation v w d.parameter

end SerrePositivity.KST.SConstruction
