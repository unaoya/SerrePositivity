module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
概要：複体の積に入る射のホモトピーを成分ごとに組み立てる。
方針：各次数の積の普遍性でホモトピー成分を定義して式を射影後に検証する。
規約：次数の自由性・積の完全性を仮定しない。
使われ方：TT §3・§8、Toën §3.2、Stacks 36.3.3 の導来逆極限の基盤。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} (P : ι → CochainComplex C ℤ) [HasProductsOfShape ι C]

/--
概要：次数ごとの積で計算する複体の積。
方針：Mathlib の評価関手による極限構成を使う。
規約：実際の非有界複体。
使われ方：TT §3、Stacks 36.3.3 の積と逆極限。
-/
def complexProduct : CochainComplex C ℤ :=
  (HomologicalComplex.coneOfHasLimitEval (Discrete.functor P)).pt

/--
概要：複体の積から各因子への射影。
方針：極限錐の脚を使う。
規約：複体の射として定義する。
使われ方：TT §3、Stacks 36.3.3 の積の比較。
-/
def complexProductπ (a : ι) : complexProduct P ⟶ P a :=
  (HomologicalComplex.coneOfHasLimitEval (Discrete.functor P)).π.app ⟨a⟩

/--
概要：複体の積へのホモトピーを成分ごとに構成する。
方針：各次数の極限に持ち上げ、ホモトピーの等式を射影で検証する。
規約：任意の小さい添字集合を許す。
使われ方：TT §3、Toën §3.2、Stacks 19.13 の K-injective な積。
-/
def homotopyIntoComplexProduct {K : CochainComplex C ℤ}
    {f g : K ⟶ complexProduct P}
    (h : ∀ a, Homotopy (f ≫ complexProductπ P a) (g ≫ complexProductπ P a)) :
    Homotopy f g where
  hom i j := limit.lift (Discrete.functor P ⋙ HomologicalComplex.eval C (.up ℤ) j)
    { pt := K.X i
      π := Discrete.natTrans (fun a => (h a.as).hom i j) }
  zero i j hij := by
    apply limit.hom_ext
    intro a
    simp only [limit.lift_π, Discrete.natTrans_app, zero_comp]
    exact (h a.as).zero i j hij
  comm i := by
    apply limit.hom_ext
    intro a
    have hc := (h a.as).comm i
    change (f ≫ complexProductπ P a.as).f i = _ at hc
    simpa [HomologicalComplex.comp_f, dNext, prevD,
      complexProduct, complexProductπ, HomologicalComplex.coneOfHasLimitEval_pt_d,
      HomologicalComplex.coneOfHasLimitEval_π_app_f,
      Preadditive.add_comp, Category.assoc, limit.lift_π,
      limMap_π, Discrete.natTrans_app] using hc

/--
概要：K-injective 複体の積は K-injective。
方針：各射影の零ホモトピーを選び、積へのホモトピーとして組み立てる。
規約：積の完全性や有界性は不要。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.13.4 の導来積。
-/
instance complexProduct_isKInjective [∀ a, (P a).IsKInjective] :
    (complexProduct P).IsKInjective where
  nonempty_homotopy_zero f hK := ⟨homotopyIntoComplexProduct P
    (fun a => (CochainComplex.IsKInjective.homotopyZero
      (f ≫ complexProductπ P a) hK).trans (.ofEq (by simp)))⟩

end SerrePositivity.KST.DerivedGeometry
