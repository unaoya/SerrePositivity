module
public import SerrePositivity.KST.SConstruction.AssemblyCoherentFactorEvaluation
public import SerrePositivity.KST.SConstruction.AssemblyInputIdentityChoices
public import SerrePositivity.KST.SConstruction.CoherentDiagramOverEdges

/-! # Coherent な全選択から元の構造射の選択への回収
概要：恒等入力射の over 頂点で全選択を評価し、元の二つの因子と構造射へ戻す。
方針：恒等成分の同型は各因子の実際の射を厳密に保持する。
規約：元の構造射と同じ成分・全基点 π 同型を保つ。
使われ方：全射列の選択を実際の K スペクトルの構造射へ接続する。
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

/-- 全射列の延長選択から回収した、元の随伴射の対象ごとの選択。 -/
def kanAssemblyCoherentChoiceAt {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (kanAssemblyCoherentChoices r F) _⦋0⦌)
    (i : I) : (kanAssemblyAdjointChoices r (F.obj i)) _⦋0⦌ :=
  (kanAssemblyInputIdentityChoicesIso r F i).hom.app (Opposite.op ⦋0⦌)
    (diagramSelectionVertex (kanAssemblyCoherentFamily r F v) (assemblyArrowMk (𝟙 i)))

/-- 全射列の逆射選択から回収した、元の比較逆射の対象ごとの選択。 -/
def oneDirectionInverseCoherentChoiceAt {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    (i : I) : (oneDirectionKanInverseChoices r (F.obj i)) _⦋0⦌ :=
  (oneDirectionInverseInputIdentityChoicesIso r F i).hom.app (Opposite.op ⦋0⦌)
    (diagramSelectionVertex (oneDirectionInverseCoherentFamily r F v) (assemblyArrowMk (𝟙 i)))

/-- 両因子の coherent な全選択から回収した、元の構造射の同時選択。 -/
def boundaryKanAssemblyCoherentChoiceAt {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u})
    (vI : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    (vE : (kanAssemblyCoherentChoices r F) _⦋0⦌) (i : I) :
    (boundaryKanAssemblyChoices r (F.obj i)) _⦋0⦌ :=
  (oneDirectionInverseCoherentChoiceAt r F vI i, kanAssemblyCoherentChoiceAt r F vE i)

/-- 同じ両因子の全選択から回収した、対象ごとの実際の随伴構造射。 -/
def boundaryKanAssemblyCoherentAdjointAt {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u})
    (vI : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    (vE : (kanAssemblyCoherentChoices r F) _⦋0⦌) (i : I) :
    (boundaryKanRealizationFunctor r).obj (F.obj i) ⟶
      (loopBoundaryKanFunctor (r + 1)).obj (F.obj i) :=
  boundaryKanAssemblyAdjointAt r (F.obj i) (boundaryKanAssemblyCoherentChoiceAt r F vI vE i)

/-- 回収した構造射は、元の随伴構造射と同じ点つきホモトピー成分。 -/
lemma boundaryKanAssemblyCoherentAdjointAt_component {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u})
    (vI : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    (vE : (kanAssemblyCoherentChoices r F) _⦋0⦌) (i : I) :
    componentOf (boundaryKanAssemblyAdjoint r (F.obj i)) =
      componentOf (boundaryKanAssemblyCoherentAdjointAt r F vI vE i) := by
  dsimp only [boundaryKanAssemblyCoherentAdjointAt]
  exact boundaryKanAssemblyAdjointAt_component r (F.obj i) (boundaryKanAssemblyCoherentChoiceAt r F vI vE i)

/-- 同じ全選択から回収した全ての構造射も、全基点 π 同型。 -/
lemma boundaryKanAssemblyCoherentAdjointAt_piIsomorphism {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u})
    (vI : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    (vE : (kanAssemblyCoherentChoices r F) _⦋0⦌) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (boundaryKanAssemblyCoherentAdjointAt r F vI vE i).right := by
  dsimp only [boundaryKanAssemblyCoherentAdjointAt]
  exact boundaryKanAssemblyAdjointAt_piIsomorphism r (F.obj i)
    (boundaryKanAssemblyCoherentChoiceAt r F vI vE i)

end SerrePositivity.KST.SConstruction
