module
public import SerrePositivity.KST.ProExcision.SetActionBar
public import SerrePositivity.KST.ProExcision.ActionNerveCoordinates

/-!
# 作用 bar の各行の積座標

概要：E_X G の bar 次数 r の行を X×G^r と同定する。
方針：各次数で始点とラベル列の全単射を使う。
規約：KST Proposition A.1。これは作用 bar 方向を固定した行で、原典の二重 bar の行との接続は別工程。
使われ方：係数と bar の方向を分けて比較写像を解析する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 概要：作用 bar の bar 次数 r の行は X×G^r。
方針：始点とラベル列の全単射の、同変な集合写像についての自然性を使う。
規約：KST Proposition A.1。群状性や逆元は不要。
使われ方：作用 bar の行の厳密な積表示。 -/
def setActionBarRowIso {G : SimplicialObject MonCat.{u}} {X : SSet.{u}}
    (A : SimplicialSetAction G X) (r : ℕ) :
    (bisimplicialSetActionBar A).flip.obj (op ⦋r⦌) ≅ X ⊗ monoidTupleSpace G r :=
  NatIso.ofComponents (fun n ↦ by
    letI := A.actionStructure n
    exact (actionNerveEquiv (G := G.obj n) (X := X.obj n) r).toIso) (by
      intro n m f
      letI := A.actionStructure n
      letI := A.actionStructure m
      apply ConcreteCategory.hom_ext
      intro p
      exact (actionNerveCoordinates_map (G.map f).hom (X.map f) (A.naturality f) p).symm)

end SerrePositivity.KST.ProExcision
