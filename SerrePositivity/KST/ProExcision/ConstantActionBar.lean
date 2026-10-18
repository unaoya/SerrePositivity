module
public import SerrePositivity.KST.ProExcision.BarTransport
public import SerrePositivity.KST.ProExcision.SetActionMorphisms

/-!
# 離散作用の bar と係数次数の自然性

概要：離散モノイドの作用を定数単体的作用にし、その bar の自然性を用意する。
方針：bar の方向だけを単体的に残し、係数のモノイドを固定する。
規約：KST Proposition A.1 の二重単体的な証明。群状性を次数ごとの群構造へ強めない。
使われ方：内側の係数次数を動かして原典の二重 bar を組み立てる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison

/-- 概要：離散モノイドへの作用を定数な単体的作用にする。
方針：全ての係数次数で同じ準同型作用を使う。
規約：KST Proposition A.1。使われ方：bar と係数の単体方向の分離。 -/
def constantSimplicialMonoidAction (G H : MonCat.{u}) (A : G →* Monoid.End H) :
    SimplicialMonoidAction ((Functor.const SimplexCategoryᵒᵖ).obj G)
      ((Functor.const SimplexCategoryᵒᵖ).obj H) where
  action _ := A
  naturality _ _ _ := rfl

/-- 概要：離散作用の係数 bar。
方針：定数な単体的作用の E_BH G を取る。
規約：KST Proposition A.1。使われ方：二重 bar の各係数次数の対象。 -/
abbrev discreteCoefficientActionBar (G H : MonCat.{u}) (A : G →* Monoid.End H) :=
  coefficientActionBar (constantSimplicialMonoidAction G H A)

/-- 概要：離散モノイドの準同型から定数単体的モノイドの射を作る。
方針：全ての次数の成分を同じ準同型とする。
規約：KST Proposition A.1。使われ方：作用 bar の係数次数の写像。 -/
def constantMonoidMap {G G' : MonCat.{u}} (f : G →* G') :
    (Functor.const SimplexCategoryᵒᵖ).obj G ⟶ (Functor.const SimplexCategoryᵒᵖ).obj G' where
  app _ := MonCat.ofHom f

/-- 概要：離散な作用の同変準同型が BH への作用の同変射を誘導する。
方針：分類空間の各射ラベルで同変条件を使う。
規約：KST Proposition A.1。使われ方：係数次数を動かす作用 bar の射。 -/
def discreteBarSetActionHom {G G' H H' : MonCat.{u}}
    {A : G →* Monoid.End H} {B : G' →* Monoid.End H'}
    (f : G →* G') (g : H →* H') (h : ∀ a x, g (A a x) = B (f a) (g x)) :
    SimplicialSetActionHom (barSetAction (constantSimplicialMonoidAction G H A))
      (barSetAction (constantSimplicialMonoidAction G' H' B)) where
  base := constantMonoidMap f
  hom := monoidBarMap (constantMonoidMap g)
  equivariant n a p := by
    apply (monoidWordEquiv H' n.unop.len).injective
    funext i
    exact h a _

/-- 概要：離散作用の係数 bar の誘導写像。
方針：分類空間への同変射を作用 bar に送る。
規約：KST Proposition A.1。使われ方：二重単体的模型の係数方向。 -/
def discreteCoefficientActionBarMap {G G' H H' : MonCat.{u}}
    {A : G →* Monoid.End H} {B : G' →* Monoid.End H'}
    (f : G →* G') (g : H →* H') (h : ∀ a x, g (A a x) = B (f a) (g x)) :
    discreteCoefficientActionBar G H A ⟶ discreteCoefficientActionBar G' H' B :=
  setActionBarMap (discreteBarSetActionHom f g h)

/-- 概要：離散作用の係数 bar の写像は恒等射を保つ。
方針：各対象と射ラベルを評価する。
規約：KST Proposition A.1。使われ方：二重 bar の恒等則。 -/
@[simp] lemma discreteCoefficientActionBarMap_id {G H : MonCat.{u}} (A : G →* Monoid.End H) :
    discreteCoefficientActionBarMap (A := A) (MonoidHom.id G) (MonoidHom.id H)
      (fun _ _ ↦ rfl) = 𝟙 _ := by
  rfl

/-- 概要：離散作用の係数 bar の写像は合成を保つ。
方針：二つの成分の合成を定義通り評価する。
規約：KST Proposition A.1。使われ方：二重 bar の係数方向の合成則。 -/
lemma discreteCoefficientActionBarMap_comp {G G' G'' H H' H'' : MonCat.{u}}
    {A : G →* Monoid.End H} {B : G' →* Monoid.End H'} {C : G'' →* Monoid.End H''}
    (f : G →* G') (g : H →* H') (h : ∀ a x, g (A a x) = B (f a) (g x))
    (f' : G' →* G'') (g' : H' →* H'') (h' : ∀ a x, g' (B a x) = C (f' a) (g' x)) :
    discreteCoefficientActionBarMap (f'.comp f) (g'.comp g) (by
      intro a x
      dsimp
      rw [h, h']) =
    discreteCoefficientActionBarMap f g h ≫ discreteCoefficientActionBarMap f' g' h' := by
  rfl

end SerrePositivity.KST.ProExcision
