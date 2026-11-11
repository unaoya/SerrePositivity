module

public import SerrePositivity.KST.Spectra.GroupCochainHomotopyDiagram
public import SerrePositivity.KST.Spectra.PointedGroupProduct

/-!
概要：関数複体の係数の後合成とホモトピー群の座標表示の自然性。
方針：各座標の評価で後合成を定義し、群の合成の関手性で比較する。
規約：添字集合は固定し、係数射のみを変える。
使われ方：Goerss–Jardine VIII §1。セルごとの Hom の係数自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SimplicialFunctionComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：関数複体の係数の射による座標ごとの後合成。
方針：各座標の評価と係数射の合成を関数複体へ持ち上げる。
規約：添字集合は任意。
使われ方：Goerss–Jardine VIII §1。セルごとの係数の射。 -/
def post (S : Type u) {X Y : SSet.{u}} (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S Y :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun s ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s ≫ f)

@[reassoc (attr := simp)]
lemma post_eval (S : Type u) {X Y : SSet.{u}} (f : X ⟶ Y) (s : S) :
    post S f ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S Y s = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s ≫ f := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval _ _

/-- 概要：係数の後合成は定数の基点の関数を保つ。
方針：各評価で元の点つき射の基点保存を使う。
規約：Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。点つき関数複体の自然性。 -/
def pointedPost (S : Type u) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedObj S X ⟶ pointedObj S Y :=
  Under.homMk (post S f.right) (by
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun (_ : S) ↦ X.hom) ≫ post S f.right = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun (_ : S) ↦ Y.hom)
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.hom_ext
    intro s
    rw [Category.assoc, post_eval, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval]
    exact Under.w f)

/-- 概要：関数複体の各座標の評価は点つき射。
方針：定数基点の関数を評価する。
規約：源と係数の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。群の座標表示の比較。 -/
def pointedEval (S : Type u) (X : PointedSimplicialSet.{u}) (s : S) :
    pointedObj S X ⟶ X := Under.homMk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X.right s) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval _ s)

@[reassoc (attr := simp)]
lemma pointedPost_eval (S : Type u) {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (s : S) :
    pointedPost S f ≫ pointedEval S Y s = pointedEval S X s ≫ f := by
  apply Under.UnderMorphism.ext
  exact post_eval S f.right s

lemma pointedHomotopyEquiv_eval (S : Type u) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedObj S X).right r (pointedObj S X).basepoint) (s : S) :
    pointedHomotopyEquiv S X r a s = pointedGroupMap r (pointedEval S X s) a := rfl

/-- 概要：関数複体の群の座標表示は係数射に自然。
方針：各座標で二つの合成射の一致を誘導群準同型へ送る。
規約：正次数群のすべてで成立。
使われ方：Goerss–Jardine VIII §1。セルの群の係数表示の自然性。 -/
theorem pointedHomotopyEquiv_natural (S : Type u) {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y) (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedObj S X).right r (pointedObj S X).basepoint) :
    pointedHomotopyEquiv S Y r (pointedGroupMap r (pointedPost S f) a) =
      fun s ↦ pointedGroupMap r f (pointedHomotopyEquiv S X r a s) := by
  funext s
  rw [pointedHomotopyEquiv_eval, pointedHomotopyEquiv_eval,
    ← pointedGroupMap_comp, pointedPost_eval, pointedGroupMap_comp]

end

end SerrePositivity.KST.Spectra.SimplicialFunctionComplex
