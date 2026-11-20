module


public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SimplicialFunctionComplex
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
概要：離散単体集合を源とする内部 Hom と座標ごとの関数複体の具体的な同型。
方針：離散因子を固定して評価し、curry と Yoneda で内部 Hom の対象を比較する。
規約：添字集合の有限性も係数の Kan 性も要求しない。
使われ方：Goerss–Jardine I §7、VIII §2。群 cochain の関数空間の π_* の計算。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.DiscreteInternalHom
end SerrePositivity.KST.Spectra.DiscreteInternalHom
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom
open _root_.SerrePositivity.KST.Spectra.DiscreteInternalHom

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (S : Type u) (X : SSet.{u})

/-- 概要：離散因子を持つ射を関数複体への射に送る。
方針：各単体で離散変数を一つの座標として保持する。
規約：パラメーターは直積の右因子。
使われ方：Goerss–Jardine I §7。内部 Hom の比較の通常の普遍性。 -/
def toFunctions {A : SSet.{u}}
    (t : (Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ A ⟶ X) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X where
  app n := ↾fun a s ↦ t.app n (s, a)
  naturality n m g := by
    apply ConcreteCategory.hom_ext
    intro a
    change (fun s ↦ t.app m (s, A.map g a)) = fun s ↦ X.map g (t.app n (s, a))
    funext s
    exact congr($(t.naturality g) (s, a))

/-- 概要：関数複体への射を離散因子を持つ射に戻す。
方針：各単体で関数を離散変数の座標で評価する。
規約：任意のパラメーターを許す。
使われ方：Goerss–Jardine I §7。内部 Hom の比較の逆の普遍性。 -/
def fromFunctions {A : SSet.{u}} (t : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) :
    (Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ A ⟶ X where
  app n := ↾fun x ↦ t.app n x.2 x.1
  naturality n m g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congr($(t.naturality g) x.2 x.1)

def familyEquiv (A : SSet.{u}) :
    ((Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ A ⟶ X) ≃
      (A ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) where
  toFun := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions S X
  invFun := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.fromFunctions S X
  left_inv t := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  right_inv t := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro a
    rfl

lemma toFunctions_pre {A B : SSet.{u}} (f : A ⟶ B)
    (t : (Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions S X (((Functor.const (SimplexCategoryᵒᵖ)).obj S ◁ f) ≫ t) =
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions S X t := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：離散集合を源とする内部 Hom への射と関数複体への射との同値。
方針：閉構造の随伴と座標による族の同値を合成する。
規約：任意のパラメーターに対する通常の射の同値。
使われ方：Goerss–Jardine I §7。関数複体の表現対象への比較。 -/
def homEquiv (A : SSet.{u}) :
    (A ⟶ (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).obj X) ≃
      (A ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) :=
  ((ihom.adjunction ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).homEquiv A X).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.familyEquiv S X A)

lemma homEquiv_pre {A B : SSet.{u}} (f : A ⟶ B)
    (t : B ⟶ (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).obj X) :
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.homEquiv S X A (f ≫ t) = f ≫ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.homEquiv S X B t := by
  change _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions S X (uncurry (f ≫ t)) = f ≫ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions S X (uncurry t)
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions_pre]

/-- 概要：離散集合を源とする内部 Hom は関数複体と同型。
方針：パラメーターに自然な Hom の同値を Yoneda で戻す。
規約：単体集合の実際の同型。
使われ方：Goerss–Jardine I §7、VIII §2。各 cochain 次数の π_* の計算。 -/
def iso : (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).obj X ≅
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X :=
  Yoneda.fullyFaithful.preimageIso
    (NatIso.ofComponents (fun A ↦ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.homEquiv S X A.unop).toIso) (fun f ↦ by
      ext t
      exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.homEquiv_pre S X f.unop t))

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
