module

public import SerrePositivity.KST.Comparison.MonoidTranslations
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexContraction
public import SerrePositivity.KST.Comparison.GrouplikeTranslations
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-!
# 単体でパラメータ付けられた平行移動

概要：単体的モノイドの元の族による左平行移動を全パラメータで構成する。
方針：作用を直積上の射とし、元の族の実ホモトピーを作用のホモトピーへ移す。
規約：Segal 1974 Proposition 1.6 の bar の面によるファイバー移送。
使われ方：単体上の作用を頂点の作用と比較し、局所化同型を証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

local instance (M : SimplicialObject MonCat.{u}) (n : SimplexCategoryᵒᵖ) :
    Monoid ((monoidSpace M).obj n) := inferInstanceAs (Monoid (M.obj n))

/--
概要：元の族による作用をパラメータとモノイドの直積の自己写像にする。
方針：第一成分を保ち、第二成分に指定された元を左から掛ける。
規約：Segal 1974 Proposition 1.6 のファイバー移送。
使われ方：bar の各行の比較写像。
-/
def monoidActionFamily (M : SimplicialObject MonCat.{u}) {X : SSet.{u}}
    (a : X ⟶ monoidSpace M) : X ⊗ monoidSpace M ⟶ X ⊗ monoidSpace M where
  app n := TypeCat.ofHom (fun p => (p.1, a.app n p.1 * p.2))
  naturality i j f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · have ha := ConcreteCategory.congr_hom (a.naturality f) p.1
      change a.app j (X.map f p.1) * (monoidSpace M).map f p.2 =
        (monoidSpace M).map f (a.app i p.1 * p.2)
      rw [show a.app j (X.map f p.1) = (monoidSpace M).map f (a.app i p.1) from ha]
      exact (map_mul (M.map f).hom (a.app i p.1) p.2).symm


/--
概要：パラメータを制限すると作用の族は自然に可換である。
方針：直積の両成分を各単体次数で評価する。
規約：Segal 1974 Proposition 1.6 のパラメータ付き作用。
使われ方：単体の貼り合わせと骨格への比較の降下。
-/
@[reassoc] theorem monoidActionFamily_naturality (M : SimplicialObject MonCat.{u})
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y ⟶ monoidSpace M) :
    f ▷ monoidSpace M ≫ monoidActionFamily M a =
      monoidActionFamily M (f ≫ a) ≫ f ▷ monoidSpace M := rfl

/--
概要：定数の元の族による作用は平行移動との直積である。
方針：直積の各単体を評価する。
規約：Segal 1974 Proposition 1.6 の頂点での作用。
使われ方：群状性から定数の族の局所化可逆性を得る。
-/
theorem monoidActionFamily_const (M : SimplicialObject MonCat.{u}) (X : SSet.{u})
    (a : M.obj (op ⦋0⦌)) : monoidActionFamily M (SSet.const (X := X) a) =
      X ◁ monoidLeftTranslation M a := rfl

/--
概要：元の族の区間写像から、作用の区間写像を作る。
方針：パラメータを保ち、区間で動く元を第二成分へ作用させる。
規約：Segal 1974 Proposition 1.6。元の族は基底へ射影しない。
使われ方：平行移動の族の実ホモトピー。
-/
def monoidActionHomotopyMap (M : SimplicialObject MonCat.{u}) {X : SSet.{u}}
    (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ monoidSpace M) :
    (X ⊗ monoidSpace M) ⊗ (Δ[1] : SSet.{u}) ⟶ X ⊗ monoidSpace M where
  app n := TypeCat.ofHom (fun p => (p.1.1, h.app n (p.1.1, p.2) * p.1.2))
  naturality i j f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · have hh := ConcreteCategory.congr_hom (h.naturality f)
        (show (X ⊗ (Δ[1] : SSet.{u})).obj i from (p.1.1, p.2))
      change h.app j (X.map f p.1.1, (Δ[1] : SSet.{u}).map f p.2) *
        (monoidSpace M).map f p.1.2 = (monoidSpace M).map f (h.app i (p.1.1, p.2) * p.1.2)
      rw [show h.app j (X.map f p.1.1, (Δ[1] : SSet.{u}).map f p.2) =
        (monoidSpace M).map f (h.app i (p.1.1, p.2)) from hh]
      exact (map_mul (M.map f).hom (h.app i (p.1.1, p.2)) p.1.2).symm


/--
概要：元の族の実ホモトピーは作用の族の実ホモトピーを誘導する。
方針：元の区間の族を各パラメータで左から作用させる。
規約：Segal 1974 Proposition 1.6 のファイバー移送のホモトピー不変性。
使われ方：単体の収縮から定数の元の作用と比較する。
-/
def monoidActionFamilyHomotopy (M : SimplicialObject MonCat.{u}) {X : SSet.{u}}
    {a b : X ⟶ monoidSpace M} (H : SSet.Homotopy a b) :
    SSet.Homotopy (monoidActionFamily M a) (monoidActionFamily M b) where
  h := monoidActionHomotopyMap M H.h
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · exact congrArg (fun x => x * p.2)
        (ConcreteCategory.congr_hom (congr_app H.h₀ n) p.1)
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · exact congrArg (fun x => x * p.2)
        (ConcreteCategory.congr_hom (congr_app H.h₁ n) p.1)
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
/--
概要：群状モノイドの定数の元の族による作用は局所化同型である。
方針：頂点の平行移動の可逆性をパラメータとの直積で保存する。
規約：Segal 1974 Proposition 1.6 の定数の作用。
使われ方：単体でパラメータ付けられた作用との比較。
-/
theorem monoidActionFamily_const_localized_isIso (M : SimplicialObject MonCat.{u})
    (hG : SimplicialMonoid.IsGrouplike M) (X : SSet.{u}) (a : M.obj (op ⦋0⦌)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M (SSet.const (X := X) a))) := by
  rw [monoidActionFamily_const]
  exact AnodyneHomotopy.whiskerLeft_anodyneQ_isIso (monoidLeftTranslation M a)
    (grouplikeTranslation_localized_isIso M hG a) X

/--
概要：群状モノイドの単体上の元の族による作用は局所化同型である。
方針：単体を零頂点へ収縮し、元の族と定数の元の族の作用を実ホモトピーで結ぶ。
規約：Segal 1974 Proposition 1.6 の単体上でのファイバー移送の比較。
使われ方：一般のパラメータの単体ごとの比較。
-/
theorem monoidActionFamily_simplex_localized_isIso (M : SimplicialObject MonCat.{u})
    (hG : SimplicialMonoid.IsGrouplike M) {n : ℕ} (a : (Δ[n] : SSet.{u}) ⟶ monoidSpace M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M a)) := by
  have hc := monoidActionFamily_const_localized_isIso M hG (Δ[n] : SSet.{u})
    (a.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0))
  have he := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)
    (monoidActionFamilyHomotopy M (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction a))
  rw [← he]
  exact hc


end SerrePositivity.KST.Comparison
