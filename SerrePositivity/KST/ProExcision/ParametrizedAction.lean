module

public import SerrePositivity.KST.ProExcision.ActionTranslations
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# 単体の族でパラメータ付けられた作用

概要：群状単体モノイドの作用を任意のパラメータの族へ拡張する。
方針：元の族のホモトピーを作用の族のホモトピーへ送り、単体の収縮で定数作用へ戻す。
規約：KST Lemma A.2 の fibration 証明に代え、単体上の収縮とセル降下を使う。
使われ方：ψ の全体での局所化同型性を標準単体上で証明する。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.KST.Comparison SerrePositivity.SimplicialModel
open scoped Simplicial
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：元の族が与えるパラメータと作用先の直積の自己写像。
方針：第一成分を固定し、第二成分にそのパラメータの元を作用させる。
規約：作用の自己同型性はまだ要求しない。
使われ方：KST Lemma A.2 の ψ とその単体への制限。 -/
def actionFamily (A : SimplicialMonoidAction G H) {X : SSet.{u}}
    (a : X ⟶ monoidSpace G) : X ⊗ monoidSpace H ⟶ X ⊗ monoidSpace H where
  app n := TypeCat.ofHom (fun p ↦ (p.1, A.action n (a.app n p.1) p.2))
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · have ha := ConcreteCategory.congr_hom (a.naturality f) p.1
      change A.action m (a.app m (X.map f p.1)) ((H.map f).hom p.2) =
        (H.map f).hom (A.action n (a.app n p.1) p.2)
      rw [show a.app m (X.map f p.1) = (G.map f).hom (a.app n p.1) from ha]
      exact (A.naturality f _ _).symm

/-- 概要：作用の族はパラメータの制限と可換。
方針：直積の二つの座標を定義通り比較する。
規約：任意のパラメータ写像。使われ方：KST Lemma A.2 のセルの貼り合わせ。 -/
@[reassoc] theorem actionFamily_naturality (A : SimplicialMonoidAction G H)
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y ⟶ monoidSpace G) :
    f ▷ monoidSpace H ≫ actionFamily A a =
      actionFamily A (f ≫ a) ≫ f ▷ monoidSpace H := rfl

/-- 概要：定数の元の族による作用は頂点作用との直積。
方針：各次数の座標を展開する。
規約：パラメータは任意。使われ方：KST Lemma A.2 の単体上の比較の終点。 -/
theorem actionFamily_const (A : SimplicialMonoidAction G H) (X : SSet.{u})
    (a : G.obj (op ⦋0⦌)) : actionFamily A (SSet.const (X := X) a) =
      X ◁ actionTranslation A a := rfl

/-- 概要：元の族の区間写像から作用の族の区間写像を作る。
方針：区間で動く元を作用先の座標へ作用させる。
規約：第一成分のパラメータは保持する。
使われ方：KST Lemma A.2 の族のホモトピー。 -/
def actionFamilyHomotopyMap (A : SimplicialMonoidAction G H) {X : SSet.{u}}
    (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ monoidSpace G) :
    (X ⊗ monoidSpace H) ⊗ (Δ[1] : SSet.{u}) ⟶ X ⊗ monoidSpace H where
  app n := TypeCat.ofHom (fun p ↦ (p.1.1, A.action n (h.app n (p.1.1, p.2)) p.1.2))
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · have hh := ConcreteCategory.congr_hom (h.naturality f)
        (show (X ⊗ (Δ[1] : SSet.{u})).obj n from (p.1.1, p.2))
      change A.action m (h.app m (X.map f p.1.1, (Δ[1] : SSet.{u}).map f p.2))
          ((H.map f).hom p.1.2) =
        (H.map f).hom (A.action n (h.app n (p.1.1, p.2)) p.1.2)
      rw [show h.app m (X.map f p.1.1, (Δ[1] : SSet.{u}).map f p.2) =
        (G.map f).hom (h.app n (p.1.1, p.2)) from hh]
      exact (A.naturality f _ _).symm

/-- 概要：元の族の実ホモトピーは作用の族の実ホモトピーを誘導する。
方針：作用写像の元の座標へ、元のホモトピーの両端等式を適用する。
規約：単体的ホモトピーを具体的に構成。
使われ方：KST Lemma A.2 の単体収縮と定数作用の比較。 -/
def actionFamilyHomotopy (A : SimplicialMonoidAction G H) {X : SSet.{u}}
    {a b : X ⟶ monoidSpace G} (h : SSet.Homotopy a b) :
    SSet.Homotopy (actionFamily A a) (actionFamily A b) where
  h := actionFamilyHomotopyMap A h.h
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · exact congrArg (fun x ↦ A.action n x p.2)
        (ConcreteCategory.congr_hom (congr_app h.h₀ n) p.1)
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · exact congrArg (fun x ↦ A.action n x p.2)
        (ConcreteCategory.congr_hom (congr_app h.h₁ n) p.1)
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：群状モノイドの定数の族の作用は anodyne 局所化で同型。
方針：頂点作用の同型を、パラメータとの直積で保存する。
規約：作用先の群性は不要。使われ方：KST Lemma A.2 の単体収縮の終点。 -/
theorem actionFamily_const_localized_isIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) (X : SSet.{u}) (a : G.obj (op ⦋0⦌)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (actionFamily A (SSet.const (X := X) a))) := by
  rw [actionFamily_const]
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map (actionTranslation A a)) :=
    (grouplikeActionIso A hG AnodyneHomotopy.anodyneQ
      (AnodyneHomotopy.map_homotopy_eq _
        (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)) a).isIso_hom
  exact AnodyneHomotopy.whiskerLeft_anodyneQ_isIso (actionTranslation A a) hi X

/-- 概要：群状モノイドの単体上の元の族の作用は anodyne 局所化で同型。
方針：単体の収縮を作用の実ホモトピーへ送り、定数の族の可逆性へ帰着する。
規約：KST Lemma A.2 の原典の fibration 証明に代わるセル降下の局所段階。
使われ方：一般のパラメータへ作用の可逆性を貼り合わせる。 -/
theorem actionFamily_simplex_localized_isIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) {n : ℕ} (a : (Δ[n] : SSet.{u}) ⟶ monoidSpace G) :
    IsIso (AnodyneHomotopy.anodyneQ.map (actionFamily A a)) := by
  have hc := actionFamily_const_localized_isIso A hG (Δ[n] : SSet.{u})
    (a.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0))
  have he := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)
    (actionFamilyHomotopy A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction a))
  rw [← he]
  exact hc

end SerrePositivity.KST.ProExcision
