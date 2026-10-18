module
public import SerrePositivity.KST.ProExcision.BarAction

/-!
# 作用 bar から半直積 bar への transport

概要：E_BH G から B(G⋉H) への比較の各単体を圏の関手として構成する。
方針：位置 i と作用圏の対象 x を対に取り、射ラベル g と標的の BH の射を組み合わせる。
規約：KST Proposition A.1、式 (A.3)。本実装の nerve の語は原典の逆順で、suffix の積は prefix と表示される。
使われ方：比較の単体的自然性と、行の積座標での同値性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：位置と作用圏から半直積の一対象圏への transport 関手。
方針：射 (i,x)→(j,y) のラベル g を (g,y(i→j)) へ送る。
規約：KST Proposition A.1。原典とは逆順の nerve 座標。群の可換性も逆元も不要。
使われ方：E_BH G の単体から B(G⋉H) の単体を作る。 -/
def actionBarTransport (A : SimplicialMonoidAction G H) (n : SimplexCategoryᵒᵖ) :=
  letI := A.actionStructure n
  letI := (barSetAction A).actionStructure n
  show Fin (n.unop.len + 1) × ActionObject (G.obj n) ((monoidBar H).obj n) ⥤
      SingleObj ((simplicialActionProduct A).obj n) from
  { obj := fun _ ↦ SingleObj.star _
    map := fun {x y} a ↦ ⟨a.2.val, y.2.val.map a.1⟩
    map_id := by
      intro x
      apply ActionProduct.ext
      · rfl
      · change x.2.val.map (𝟙 x.1) = (1 : H.obj n)
        rw [x.2.val.map_id]
        rfl
    map_comp := by
      intro x y z a b
      apply ActionProduct.ext
      · rfl
      · change z.2.val.map (a.1 ≫ b.1) =
          (show H.obj n from z.2.val.map b.1) * A.action n b.2.val (y.2.val.map a.1)
        rw [z.2.val.map_comp]
        have hz := congrArg (fun p : (monoidBar H).obj n ↦ p.map a.1) b.2.property
        change A.action n b.2.val (y.2.val.map a.1) = z.2.val.map a.1 at hz
        rw [hz]
        rfl }

/-- 概要：作用 bar E_BH G から半直積の分類空間への単体的比較。
方針：単体の位置と作用圏への射列を対にし、transport 関手と合成する。
規約：KST Proposition A.1、式 (A.3)。原典とは逆順の語の座標で同じ半直積の積を使う。
使われ方：行ごとの群状作用の同値性を対角へ移す比較射。 -/
def actionBarComparison (A : SimplicialMonoidAction G H) :
    coefficientActionBar A ⟶ monoidBar (simplicialActionProduct A) where
  app n := by
    letI := A.actionStructure n
    letI := (barSetAction A).actionStructure n
    exact ↾fun p ↦ (𝟭 (Fin (n.unop.len + 1))).prod' p ⋙ actionBarTransport A n
  naturality n m f := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    letI := (barSetAction A).actionStructure n
    letI := (barSetAction A).actionStructure m
    apply ConcreteCategory.hom_ext
    intro p
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j a
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply ActionProduct.ext <;> rfl

end SerrePositivity.KST.ProExcision
