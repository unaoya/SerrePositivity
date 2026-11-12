module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron
public import SerrePositivity.KST.SConstruction.AnodyneExtensionChoices

/-! # 元の二つの合成面を保持する終辺消去の全外ホーン
概要：共通の終辺と対角を持つ二面を、同じ退化面とともに三次外ホーンへ貼る。
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
  {a d : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
  (T : SSet.Edge.CompStruct a b c) (U : SSet.Edge.CompStruct d b c)

/-- 元の二面と共通終辺の退化面を持つ同じ全三面族。 -/
def triangleRightCancellationFaces (j : Fin 4) (_ : j ≠ 3) : (Δ[2] : SSet.{u}) ⟶ E :=
  ![SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp b).simplex,
    SSet.yonedaEquiv.symm U.simplex, SSet.yonedaEquiv.symm T.simplex,
    SSet.yonedaEquiv.symm T.simplex] j

/-- 元の全三面は、同じ三次外ホーンの共有全辺で厳密に一致する。 -/
lemma triangleRightCancellationFaces_compatible :
    horn.IsCompatible (triangleRightCancellationFaces T U) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
    | exact (hj rfl).elim
    | exact (hk rfl).elim
    | exact False.elim ((show ¬ _ from by decide) hjk)
    | skip
  · change stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp b).simplex =
      stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm U.simplex
    rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm,
      SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  · change stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp b).simplex =
      stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm T.simplex
    rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
      SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  · change stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm U.simplex =
      stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm T.simplex
    rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
      SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]

/-- 元の二面と退化面の全三次外ホーン。 -/
def triangleRightCancellationHorn : (Λ[3, 3] : SSet.{u}) ⟶ E :=
  (triangleRightCancellationFaces_compatible T U).exists_desc.choose

/-- 全外ホーンの各面は入力した同じ全二面そのもの。 -/
lemma triangleRightCancellationHorn_face (j : Fin 4) (hj : j ≠ 3) :
    horn.ι (3 : Fin 4) j hj ≫ triangleRightCancellationHorn T U =
      triangleRightCancellationFaces T U j hj :=
  (triangleRightCancellationFaces_compatible T U).exists_desc.choose_spec j hj

/-- 元の二面を保持する終辺消去の全四面体の単体的選択空間。 -/
def triangleRightCancellationChoices : SSet.{u} :=
  anodyneExtensionChoices (horn 3 (3 : Fin 4)).ι (triangleRightCancellationHorn T U)

/-- 元の全二面を指定した終辺消去の選択空間は可縮 Kan。 -/
lemma triangleRightCancellationChoices_isContractibleKan [KanComplex E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (triangleRightCancellationChoices T U) :=
  anodyneExtensionChoices_isContractibleKan _ (anodyneExtensions.horn_ι (3 : Fin 4)) _

/-- 既存の全高次パラメータを保持して、同じ二面を持つ四面体の選択を延長できる。 -/
lemma triangleRightCancellationChoices_relative_lifting [KanComplex E]
    {P Q : SSet.{u}} (j : P ⟶ Q) [Mono j]
    (q : P ⟶ triangleRightCancellationChoices T U) :
    ∃ q' : Q ⟶ triangleRightCancellationChoices T U, j ≫ q' = q :=
  anodyneExtensionChoices_relative_lifting _ (anodyneExtensions.horn_ι (3 : Fin 4)) _ j q

/-- 選択した終辺消去の四面体の同じ全実写像。 -/
def triangleRightCancellationAt (v : (triangleRightCancellationChoices T U) _⦋0⦌) :
    (Δ[3] : SSet.{u}) ⟶ E :=
  anodyneExtensionAt _ (triangleRightCancellationHorn T U) v

/-- 同じ四面体の全指定面は元の二面と退化面を厳密に保持する。 -/
lemma triangleRightCancellationAt_face (v : (triangleRightCancellationChoices T U) _⦋0⦌)
    (j : Fin 4) (hj : j ≠ 3) :
    stdSimplex.δ j ≫ triangleRightCancellationAt T U v =
      triangleRightCancellationFaces T U j hj := by
  rw [← horn.ι_ι_assoc (3 : Fin 4) j hj, triangleRightCancellationAt,
    anodyneExtensionAt_fac, triangleRightCancellationHorn_face]

end SerrePositivity.KST.SConstruction
