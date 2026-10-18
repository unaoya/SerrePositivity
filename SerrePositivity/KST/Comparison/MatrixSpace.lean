module

public import SerrePositivity.KST.Comparison.DoldKanGL
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# 単体的環の全行列の単体集合

概要：全行列を単体的環として束ね、係数の Kan 充填を行列へまとめる。
方針：係数環の射を各成分に作用させ、各係数のホーン充填を同時に選ぶ。
規約：KST 式 (2.2)、Lemma 2.13 の全行列側。
使われ方：可逆成分の包含による正次数の群同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：単体的環上の有限正方行列の単体的環。
方針：各次数の行列環と係数ごとの環準同型を使う。
規約：rank r は固定する。
使われ方：全行列の台単体集合。
-/
def matrixRingObject (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    SimplicialObject RingCat.{u} where
  obj n := RingCat.of (Matrix (Fin r) (Fin r) (A.obj n))
  map f := RingCat.ofHom (A.map f).hom.mapMatrix
  map_id n := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    apply Matrix.ext
    intro i j
    change (A.map (𝟙 n)).hom (a i j) = a i j
    simp
  map_comp f g := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    apply Matrix.ext
    intro i j
    change (A.map (f ≫ g)).hom (a i j) = (A.map g).hom ((A.map f).hom (a i j))
    rw [A.map_comp]
    rfl

/--
概要：全行列の台単体集合。
方針：行列の単体的環の忘却を使う。
規約：行列の各単体次数での可逆性は要求しない。
使われ方：ĜL の部分単体集合としての比較先。
-/
abbrev matrixSpace (A : SimplicialObject RingCat.{u}) (r : ℕ) : SSet.{u} :=
  ringSpace (matrixRingObject A r)

/--
概要：全行列から一つの係数を取り出す単体写像。
方針：各次数で同じ行・列を評価する。
規約：係数の乗法準同型とは主張しない。
使われ方：ホーンの係数ごとの充填。
-/
def matrixEntryMap (A : SimplicialObject RingCat.{u}) (r : ℕ) (i j : Fin r) :
    matrixSpace A r ⟶ ringSpace A where
  app _ := TypeCat.ofHom (fun a => a i j)
  naturality _ _ _ := rfl

/--
概要：係数ごとの単体写像を行列値の単体写像へまとめる。
方針：各次数の像を行列の各成分として定義する。
規約：定義域は任意の単体集合。
使われ方：有限個のホーン充填の組み合わせ。
-/
def matrixMapOfEntries (A : SimplicialObject RingCat.{u}) (r : ℕ) {X : SSet.{u}}
    (f : Fin r → Fin r → (X ⟶ ringSpace A)) : X ⟶ matrixSpace A r where
  app n := TypeCat.ofHom (fun x i j => (f i j).app n x)
  naturality {m n} g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Matrix.ext
    intro i j
    exact congrArg (fun t => t x) ((f i j).naturality g)

/--
概要：台単体集合が Kan である単体的環の全行列も Kan である。
方針：ホーンの各係数を別々に充填し、行列値の射へまとめる。
規約：環の Kan 性は明示的な仮定。π_n の定義は用いない。
使われ方：ĜL の可逆成分の Kan 性の入力。
-/
instance matrixSpace_kanComplex (A : SimplicialObject RingCat.{u})
    [KanComplex (ringSpace A)] (r : ℕ) : KanComplex (matrixSpace A r) := by
  rw [KanComplex.iff]
  intro n k f hf
  have hentry (i j : Fin r) := KanComplex.hornFilling (hf.desc ≫ matrixEntryMap A r i j)
  choose t ht using hentry
  refine ⟨matrixMapOfEntries A r t, fun l hl => ?_⟩
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply Matrix.ext
  intro i j
  have he : stdSimplex.δ l ≫ t i j = f l hl ≫ matrixEntryMap A r i j := by
    calc
      _ = horn.ι k l hl ≫ (horn (n + 1) k).ι ≫ t i j := by rw [horn.ι_ι_assoc]
      _ = horn.ι k l hl ≫ hf.desc ≫ matrixEntryMap A r i j := by rw [← ht i j]
      _ = _ := by rw [← Category.assoc, hf.ι_desc]
  exact congrArg (fun q => q.app d x) he

end SerrePositivity.KST.Comparison
