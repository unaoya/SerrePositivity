module
public import SerrePositivity.KST.ProExcision.SetActionBar
public import SerrePositivity.KST.ProExcision.SimplicialAction
public import SerrePositivity.KST.Comparison.BarSegal

/-!
# 分類空間への誘導作用

概要：モノイドへの準同型作用から、その分類空間への集合の作用を作る。
方針：各 nerve 単体の射列を作用の一対象関手で後合成する。
規約：KST Proposition A.1 の BH。非可換な H の面をモノイド準同型として扱わない。
使われ方：係数 C(H) を持つ作用 bar E_BH G の具体的な定義。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 概要：モノイドへの作用が nerve の各単体に誘導する作用。
方針：射列の各ラベルに自己準同型を適用する。
規約：KST Proposition A.1。使われ方：分類空間上の単体的な集合の作用。 -/
def monoidNerveAction (G H : MonCat.{u}) (A : G →* Monoid.End H) (n : ℕ) :
    G →* Function.End ((nerve (SingleObj H)) _⦋n⦌) where
  toFun g p := p ⋙ SingleObj.mapHom H H (A g)
  map_one' := by
    funext p
    apply (monoidWordEquiv H n).injective
    funext i
    change A 1 (monoidWordLabels H p i) = monoidWordLabels H p i
    rw [map_one]
    rfl
  map_mul' g g' := by
    funext p
    apply (monoidWordEquiv H n).injective
    funext i
    change A (g * g') (monoidWordLabels H p i) =
      A g (A g' (monoidWordLabels H p i))
    rw [map_mul]
    rfl

/-- 概要：単体的モノイドへの作用から分類空間への単体的集合の作用を得る。
方針：各次数の nerve 作用を取り、元の作用の自然性を任意の射ラベルに使う。
規約：KST Proposition A.1 の BH への作用。
使われ方：作用 bar と半直積の分類空間との比較。 -/
def barSetAction {G H : SimplicialObject MonCat.{u}} (A : SimplicialMonoidAction G H) :
    SimplicialSetAction G (monoidBar H) where
  action n := monoidNerveAction (G.obj n) (H.obj n) (A.action n) n.unop.len
  naturality {n m} f a p := by
    apply (monoidWordEquiv (H.obj m) m.unop.len).injective
    funext i
    exact A.naturality f a _

/-- 概要：分類空間 BH を係数の作用先とする bar E_BH G。
方針：分類空間への単体的集合の作用の bar を取る。
規約：KST Proposition A.1 の左辺の幾何的模型。
使われ方：ℤE_BH G の複体模型と B(G⋉H) の比較。 -/
abbrev coefficientActionBar {G H : SimplicialObject MonCat.{u}}
    (A : SimplicialMonoidAction G H) : SSet.{u} :=
  setActionBar (barSetAction A)

end SerrePositivity.KST.ProExcision
