module

public import SerrePositivity.KST.Spectra.ExponentialSpecifiedComposition

/-!
概要：前半が指定部分を固定する二つの実区間を、後半の全射影を保持して合成する。
方針：後半の射影辺の左単位三角形を指定し、同じ二辺固定の相対内ホーンを充填する。
規約：後半の非定値な射影を選び直さない。使われ方：交換自然性と実入力正方形の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.ExponentialPaths
variable {A B E : SSet.{u}} (i : B ⟶ A) {f g k : A ⟶ E}
  (H : SSet.Homotopy f g) (V : SSet.Homotopy g k)

/-- 後半の同じ射影辺へ左単位を合成する、指定された実退化三角形。 -/
def initialRelativeTriangle : (Δ[2] : SSet.{u}) ⟶ (ihom B).obj E :=
  SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp
    ((edge V).map ((MonoidalClosed.pre i).app E))).simplex

/-- 元の二辺と後半の実射影の左単位三角形を保持する、相対合成データ。 -/
abbrev InitialRelativeComposite := SpecifiedComposite i H V (initialRelativeTriangle i V)

/-- 前半の射影が定数なら、後半の指定射影を全区間で保つ実合成を構成する。 -/
def InitialRelativeComposite.choose [Mono i] [KanComplex E]
    (hH : i ▷ (Δ[1] : SSet.{u}) ≫ H.h = fst B (Δ[1] : SSet.{u}) ≫ i ≫ g) :
    InitialRelativeComposite i H V := by
  let p := (MonoidalClosed.pre i).app E
  have hid (x : ((ihom B).obj E) _⦋0⦌) :
      SSet.yonedaEquiv.symm (SSet.Edge.id x).edge = SSet.const x := by
    have he := congrArg (fun e : ((ihom B).obj E).Edge x x => SSet.yonedaEquiv.symm e.edge)
      (FundamentalLoop.edge_const (X := (ihom B).obj E) (x := x))
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (SSet.const x)) = _ at he
    rw [Equiv.symm_apply_apply] at he
    exact he.symm
  apply SpecifiedComposite.choose
  · change curry H.h ≫ p = stdSimplex.δ (2 : Fin 3) ≫
      SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp ((edge V).map p)).simplex
    rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm, hid, vertex_pre,
      curry_pre_app, hH, curry_fst]
  · change curry V.h ≫ p = stdSimplex.δ (0 : Fin 3) ≫
      SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp ((edge V).map p)).simplex
    rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm, SSet.Edge.map_edge,
      ← SSet.yonedaEquiv_symm_comp, edge_path]

/-- 後半の射影の左単位三角形の対角辺は、同じ後半の実辺全体。 -/
lemma initialRelativeTriangle_one :
    stdSimplex.δ (1 : Fin 3) ≫ initialRelativeTriangle i V =
      curry V.h ≫ (MonoidalClosed.pre i).app E := by
  rw [initialRelativeTriangle, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
    SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp, edge_path]

/-- 合成後の指定部分上の全区間は、後半の元の非定値な区間そのもの。 -/
lemma InitialRelativeComposite.restriction (C : InitialRelativeComposite i H V) :
    i ▷ (Δ[1] : SSet.{u}) ≫ C.homotopy.h = i ▷ (Δ[1] : SSet.{u}) ≫ V.h := by
  rw [SpecifiedComposite.restriction, initialRelativeTriangle_one, uncurry_pre_app, uncurry_curry]

end SerrePositivity.KST.Spectra.ExponentialPaths
