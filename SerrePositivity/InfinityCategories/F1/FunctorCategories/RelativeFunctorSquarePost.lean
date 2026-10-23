module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorVertices

/-!
概要：底を変える可換四角形による相対関手空間の後合成。
方針：全空間の射を評価に後合成し、底の射との可換性から相対 curry する。
規約：元の底と像の底は異なってよく、充填性は不要。
使われ方：Kerodon Remark 5.6.2.5、unstraightening の底変換と写像空間の比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底を変える可換四角形は相対関手空間の射を与える。
方針：普遍的な評価に全空間の射 f を後合成し、底を a≫k に変える。
規約：可換性は f≫q=p≫k という厳密な等式で指定する。
使われ方：Kerodon Remark 5.6.2.5、底の異なる fibration の間の比較の作用。 -/
def relativeFunctorSquarePost {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D)
    (f : E ⟶ F) (hf : f ≫ q = p ≫ k) (a : A ⟶ B) :
    relativeFunctorSpace p a ⟶ relativeFunctorSpace q (a ≫ k) :=
  relativeFunctorCurry (relativeFunctorUncurry (𝟙 (relativeFunctorSpace p a)) ≫ f) (by
    rw [Category.assoc, hf, ← Category.assoc, relativeFunctorUncurry_projection,
      Category.assoc])

/-- 概要：可換四角形の相対後合成の評価は全空間の射への後合成。
方針：相対 uncurry のパラメーター自然性と curry の往復を使う。
規約：任意のパラメーター T からの族を扱う。
使われ方：Kerodon Remark 5.6.2.5、底変換の比較四角形の族での計算則。 -/
lemma relativeFunctorSquarePost_uncurry {A E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D)
    (f : E ⟶ F) (hf : f ≫ q = p ≫ k) (a : A ⟶ B)
    (g : T ⟶ relativeFunctorSpace p a) :
    relativeFunctorUncurry (g ≫ relativeFunctorSquarePost p q k f hf a) =
      relativeFunctorUncurry g ≫ f := by
  rw [relativeFunctorUncurry_naturality, relativeFunctorSquarePost,
    relativeFunctorUncurry_curry, ← Category.assoc]
  have h := relativeFunctorUncurry_naturality (𝟙 (relativeFunctorSpace p a)) g
  rw [Category.comp_id] at h
  rw [← h]

/-- 概要：可換四角形の後合成は通常の相対関手頂点を合成した射の頂点へ写す。
方針：相対頂点の内部 Hom 成分を計算する。
規約：像の底の図式は a≫k。
使われ方：Kerodon Remark 5.6.2.5、写像空間上の作用と通常の射の整合性。 -/
lemma relativeFunctorSquarePost_vertex {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D)
    (f : E ⟶ F) (hf : f ≫ q = p ≫ k) (a : A ⟶ B)
    (g : A ⟶ E) (hg : g ≫ p = a) :
    (relativeFunctorSquarePost p q k f hf a).app _ (relativeFunctorVertex p a g hg) =
      relativeFunctorVertex q (a ≫ k) (g ≫ f)
        (by rw [Category.assoc, hf, ← Category.assoc, hg]) := by
  apply Subtype.ext
  rfl

/-- 概要：底上の前合成を展開すると、始域の全空間の射による制限になる。
方針：各次数で内部 Hom の前合成と評価を計算する。
規約：始域の底への射は Over 圏の射の可換性で同定する。
使われ方：Kerodon §5.3.1、写像空間の底変換の自然性の前合成側。 -/
lemma relativeFunctorOverPre_uncurry {E B T : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) (g : T ⟶ relativeFunctorSpace p b.hom) :
    relativeFunctorUncurry (g ≫ relativeFunctorOverPre p f) =
      (f.left ▷ T) ≫ relativeFunctorUncurry g := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  rfl

end SerrePositivity.InfinityCategories
