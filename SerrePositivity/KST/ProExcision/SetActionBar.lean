module
public import SerrePositivity.KST.ProExcision.ActionCategory
public import SerrePositivity.KST.Comparison.GroupCompletion

/-!
# 単体的集合への作用の bar

概要：単体的モノイドが一般の単体的集合へ作用する場合の E_X G を構成する。
方針：作用の圏を各次数で作り、二重 nerve の対角を取る。
規約：KST Proposition A.1。BH の面は非可換群ではモノイド準同型ではないため、集合への作用を使う。
使われ方：E_BH G と半直積の分類空間との比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite

/-- 概要：単体的モノイドによる単体的集合への作用。
方針：各次数の作用を関数の自己写像のモノイドへの準同型で保持する。
規約：KST Proposition A.1 の BH を作用先にできる集合の界面。
使われ方：作用先の単体射にモノイド構造を要求しない bar。 -/
structure SimplicialSetAction (G : SimplicialObject MonCat.{u}) (X : SSet.{u}) where
  action (n : SimplexCategoryᵒᵖ) : G.obj n →* Function.End (X.obj n)
  naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (a : G.obj n) (x : X.obj n) :
    X.map f (action n a x) = action m (G.map f a) (X.map f x)

variable {G : SimplicialObject MonCat.{u}} {X : SSet.{u}}

/-- 概要：各単体次数の集合への作用を通常の MulAction として取り出す。
方針：準同型の単位と積の保存を評価する。
規約：大域インスタンスには登録しない。使われ方：KST Prop A.1 の作用の圏。 -/
@[instance_reducible] def SimplicialSetAction.actionStructure (A : SimplicialSetAction G X)
    (n : SimplexCategoryᵒᵖ) : MulAction (G.obj n) (X.obj n) where
  smul a x := A.action n a x
  one_smul x := congrFun (A.action n).map_one x
  mul_smul a b x := congrFun ((A.action n).map_mul a b) x

/-- 概要：単体的集合への作用の単体的な作用圏。
方針：単体射から同変な集合写像を作り、作用圏へ送る。
規約：KST Proposition A.1 の E_X G。使われ方：二重 nerve の第一方向。 -/
def simplicialSetActionCategory (A : SimplicialSetAction G X) : SimplicialObject Cat.{u,u} where
  obj n := letI := A.actionStructure n; Cat.of (ActionObject (G.obj n) (X.obj n))
  map {n m} f := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    exact (actionCategoryMap (G.map f).hom (X.map f) (A.naturality f)).toCatHom
  map_id n := by
    letI := A.actionStructure n
    change (actionCategoryMap (G.map (𝟙 n)).hom (X.map (𝟙 n)) _).toCatHom = _
    simp only [G.map_id, X.map_id]
    rfl
  map_comp {n m k} f g := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    letI := A.actionStructure k
    change (actionCategoryMap (G.map (f ≫ g)).hom (X.map (f ≫ g)) _).toCatHom = _
    simp only [G.map_comp, X.map_comp]
    rfl

/-- 概要：単体的集合への作用の二重 bar。
方針：単体的作用圏へ nerve 関手を合成する。
規約：KST Proposition A.1 の二つの単体方向。
使われ方：行ごとの比較を対角へ移す前の模型。 -/
def bisimplicialSetActionBar (A : SimplicialSetAction G X) : SimplicialObject SSet.{u} :=
  simplicialSetActionCategory A ⋙ nerveFunctor

/-- 概要：単体的集合への作用の bar E_X G。
方針：二重作用 bar の対角を取る。
規約：KST Proposition A.1。使われ方：X=BH の係数付き群ホモロジー模型。 -/
def setActionBar (A : SimplicialSetAction G X) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (bisimplicialSetActionBar A)

end SerrePositivity.KST.ProExcision
