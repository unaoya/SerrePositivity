module

public import SerrePositivity.KST.ProExcision.SimplicialAction

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# 単体的作用の同変な射と自明射

概要：同変な単体的モノイドの射から半直積の射を構成する。
方針：各次数の同変準同型の半直積写像を自然に束ねる。
規約：基底のモノイド G は固定。自明射は H の全ての元を単位へ送る。
使われ方：KST Prop A.1 の自然性と Lemma A.4 の相対項の零化。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
variable {G H H' : SimplicialObject MonCat.{u}}

/-- 概要：同じモノイド G の二つの単体的作用の間の同変射。
方針：作用先の単体的準同型に、各次数の作用との可換性を付ける。
規約：証明すべきホモロジー命題を含まない数学的データ。
使われ方：KST Lemma A.4 の同変な群の射 φ。 -/
structure SimplicialActionHom (A : SimplicialMonoidAction G H) (B : SimplicialMonoidAction G H') where
  /-- 概要：作用先の単体的準同型。方針：自然変換。規約：モノイドの射。使われ方：KST App. A の φ。 -/
  hom : H ⟶ H'
  /-- 概要：作用との同変性。方針：各次数で等式を指定。
  規約：全てのモノイド元で成立。使われ方：KST App. A の半直積の誘導射。 -/
  equivariant : ∀ n (a : G.obj n) (b : H.obj n),
    (hom.app n).hom (A.action n a b) = B.action n a ((hom.app n).hom b)

/-- 概要：同変射が誘導する単体的半直積の射。
方針：G 成分は恒等射、H 成分は同変準同型とする。
規約：単体的モノイドの実際の自然変換。
使われ方：KST Prop A.1・Lemma A.4 の半直積の誘導写像。 -/
def simplicialActionProductMap {A : SimplicialMonoidAction G H}
    {B : SimplicialMonoidAction G H'} (f : SimplicialActionHom A B) :
    simplicialActionProduct A ⟶ simplicialActionProduct B where
  app n := by
    letI := A.actionStructure n
    letI := B.actionStructure n
    exact MonCat.ofHom (actionProductMap (MonoidHom.id _) (f.hom.app n).hom (f.equivariant n))
  naturality n m k := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    letI := B.actionStructure n
    letI := B.actionStructure m
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply ActionProduct.ext
    · rfl
    · exact congrArg (fun g ↦ g.hom x.fiber) (f.hom.naturality k)

/-- 概要：半直積の誘導射は基底の標準包含と可換。
方針：H 成分の単位保存を使う。
規約：基底 G の写像は恒等。使われ方：KST Lemma A.4 の相対項への降下。 -/
theorem simplicialActionProductSection_map {A : SimplicialMonoidAction G H}
    {B : SimplicialMonoidAction G H'} (f : SimplicialActionHom A B) :
    simplicialActionProductSection A ≫ simplicialActionProductMap f = simplicialActionProductSection B := by
  apply NatTrans.ext
  funext n
  letI := A.actionStructure n
  letI := B.actionStructure n
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro a
  apply ActionProduct.ext
  · rfl
  · exact map_one (f.hom.app n).hom

/-- 概要：半直積の誘導射は基底への射影と可換。
方針：G 成分を定義通り比較する。
規約：基底の射は恒等。使われ方：KST App. A の分裂相対項の自然性。 -/
@[simp] theorem simplicialActionProductMap_projection {A : SimplicialMonoidAction G H}
    {B : SimplicialMonoidAction G H'} (f : SimplicialActionHom A B) :
    simplicialActionProductMap f ≫ simplicialActionProductProjection B =
      simplicialActionProductProjection A := by rfl

/-- 概要：二つの作用の間の単位への自明射。
方針：作用先の全ての元を単位へ送り、作用の単位保存を使う。
規約：群の自明準同型に一致する。使われ方：KST Definition A.3 の C(e)。 -/
def SimplicialActionHom.trivial (A : SimplicialMonoidAction G H)
    (B : SimplicialMonoidAction G H') : SimplicialActionHom A B where
  hom :=
    { app n := MonCat.ofHom (1 : H.obj n →* H'.obj n)
      naturality n m k := by
        apply MonCat.hom_ext
        apply MonoidHom.ext
        intro x
        exact (map_one (H'.map k).hom).symm }
  equivariant n a b := by
    change (1 : H'.obj n) = B.action n a 1
    exact (map_one _).symm

/-- 概要：自明射が誘導する半直積の射は、基底への射影と包含の合成。
方針：G 成分は保持し、H 成分は単位となることを比較する。
規約：単体的モノイドの射の等式。
使われ方：KST Lemma A.4 の C(e) が相対項で零となること。 -/
theorem simplicialActionProductMap_trivial (A : SimplicialMonoidAction G H)
    (B : SimplicialMonoidAction G H') :
    simplicialActionProductMap (SimplicialActionHom.trivial A B) =
      simplicialActionProductProjection A ≫ simplicialActionProductSection B := by rfl

end SerrePositivity.KST.ProExcision
