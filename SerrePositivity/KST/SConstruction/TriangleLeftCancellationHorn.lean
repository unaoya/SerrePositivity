module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CompositionTripleTetrahedron
public import SerrePositivity.KST.SConstruction.AnodyneExtensionChoices

/-! # 元の二つの合成面を保持する始辺消去の全外ホーン
概要：共通の始辺と対角を持つ二面を、同じ退化面とともに三次外ホーンへ貼る。
方針：三つの全二面の共有辺の厳密な一致を使う。
規約：全二面を保持し、合成類の等号だけを指定する充填にしない。
使われ方：十二面の辺路の消去を、相対延長可能な四面体の選択へ置き換える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {E : SSet.{u}} {x y z : E _⦋0⦌}
  {a : E.Edge x y} {b d : E.Edge y z} {c : E.Edge x z}
  (T : SSet.Edge.CompStruct a b c) (U : SSet.Edge.CompStruct a d c)

/-- 元の二面と共通始辺の退化面を持つ同じ全三面族。 -/
def triangleLeftCancellationFaces (j : Fin 4) (_ : j ≠ 0) : (Δ[2] : SSet.{u}) ⟶ E :=
  ![SSet.yonedaEquiv.symm T.simplex, SSet.yonedaEquiv.symm U.simplex,
    SSet.yonedaEquiv.symm T.simplex,
    SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId a).simplex] j

/-- 元の全三面は、同じ三次外ホーンの共有全辺で厳密に一致する。 -/
lemma triangleLeftCancellationFaces_compatible :
    horn.IsCompatible (triangleLeftCancellationFaces T U) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
    | exact (hj rfl).elim
    | exact (hk rfl).elim
    | exact False.elim ((show ¬ _ from by decide) hjk)
    | skip
  · change stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm U.simplex =
      stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm T.simplex
    rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
      SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  · change stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm U.simplex =
      stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId a).simplex
    rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm,
      SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  · change stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm T.simplex =
      stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId a).simplex
    rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm,
      SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]

/-- 元の二面と退化面の全三次外ホーン。 -/
def triangleLeftCancellationHorn : (Λ[3, 0] : SSet.{u}) ⟶ E :=
  (triangleLeftCancellationFaces_compatible T U).exists_desc.choose

/-- 全外ホーンの各面は入力した同じ全二面そのもの。 -/
lemma triangleLeftCancellationHorn_face (j : Fin 4) (hj : j ≠ 0) :
    horn.ι (0 : Fin 4) j hj ≫ triangleLeftCancellationHorn T U =
      triangleLeftCancellationFaces T U j hj :=
  (triangleLeftCancellationFaces_compatible T U).exists_desc.choose_spec j hj

/-- 元の二面を保持する始辺消去の全四面体の単体的選択空間。 -/
def triangleLeftCancellationChoices : SSet.{u} :=
  anodyneExtensionChoices (horn 3 (0 : Fin 4)).ι (triangleLeftCancellationHorn T U)

/-- 元の全二面を指定した始辺消去の選択空間は可縮 Kan。 -/
lemma triangleLeftCancellationChoices_isContractibleKan [KanComplex E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (triangleLeftCancellationChoices T U) :=
  anodyneExtensionChoices_isContractibleKan _ (anodyneExtensions.horn_ι (0 : Fin 4)) _

/-- 既存の全高次パラメータを保持して、同じ二面を持つ四面体の選択を延長できる。 -/
lemma triangleLeftCancellationChoices_relative_lifting [KanComplex E]
    {P Q : SSet.{u}} (j : P ⟶ Q) [Mono j]
    (q : P ⟶ triangleLeftCancellationChoices T U) :
    ∃ q' : Q ⟶ triangleLeftCancellationChoices T U, j ≫ q' = q :=
  anodyneExtensionChoices_relative_lifting _ (anodyneExtensions.horn_ι (0 : Fin 4)) _ j q

/-- 選択した始辺消去の四面体の同じ全実写像。 -/
def triangleLeftCancellationAt (v : (triangleLeftCancellationChoices T U) _⦋0⦌) :
    (Δ[3] : SSet.{u}) ⟶ E :=
  anodyneExtensionAt _ (triangleLeftCancellationHorn T U) v

/-- 同じ四面体の全指定面は元の二面と退化面を厳密に保持する。 -/
lemma triangleLeftCancellationAt_face (v : (triangleLeftCancellationChoices T U) _⦋0⦌)
    (j : Fin 4) (hj : j ≠ 0) :
    stdSimplex.δ j ≫ triangleLeftCancellationAt T U v =
      triangleLeftCancellationFaces T U j hj := by
  rw [← horn.ι_ι_assoc (0 : Fin 4) j hj, triangleLeftCancellationAt,
    anodyneExtensionAt_fac, triangleLeftCancellationHorn_face]

end SerrePositivity.KST.SConstruction
