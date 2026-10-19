module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomChainMap
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-! # pinched 写像空間の鎖写像に関する関手則

概要：Hom 鎖写像による実 pinched 写像は恒等と合成を保ち、鎖同型を実同型に送る。
方針：実単体の線形表示で全成分を照合する。
規約：異なる dg 圏の固定 Hom 同士を扱う。使われ方：一般準同型の全射 span 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E T : Type v}
  [DGCategory A D] [DGCategory A E] [DGCategory A T]
variable {x y : D} {x' y' : E} {x'' y'' : T}

/-- 恒等 Hom 鎖写像が誘導する実 pinched 写像は恒等。 -/
lemma pinchedHomChainMap_id :
    pinchedHomChainMap (𝟙 (homObject A D x y)) = 𝟙 (DGNerve.pinchedHom A D x y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply (linearEquiv x y n.unop.len).injective
  change toLinearSimplex (pinchedHomChainMapSimplex _ s) = toLinearSimplex s
  rw [pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  rfl

/-- Hom 鎖写像の合成が誘導する実 pinched 写像は実際の合成。 -/
lemma pinchedHomChainMap_comp
    (φ : homObject A D x y ⟶ homObject A E x' y')
    (ψ : homObject A E x' y' ⟶ homObject A T x'' y'') :
    pinchedHomChainMap (φ ≫ ψ) = pinchedHomChainMap φ ≫ pinchedHomChainMap ψ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply (linearEquiv x'' y'' n.unop.len).injective
  change toLinearSimplex (pinchedHomChainMapSimplex _ s) =
    toLinearSimplex (pinchedHomChainMapSimplex ψ (pinchedHomChainMapSimplex φ s))
  rw [pinchedHomChainMapSimplex_linear, pinchedHomChainMapSimplex_linear]
  rw [pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  rfl

/-- Hom 複体の実同型は実 pinched 写像空間の同型を誘導する。 -/
lemma pinchedHomChainMap_isIso
    (φ : homObject A D x y ⟶ homObject A E x' y') [IsIso φ] :
    IsIso (pinchedHomChainMap φ) := by
  let e : DGNerve.pinchedHom A D x y ≅ DGNerve.pinchedHom A E x' y' := {
    hom := pinchedHomChainMap φ
    inv := pinchedHomChainMap (inv φ)
    hom_inv_id := by rw [← pinchedHomChainMap_comp, IsIso.hom_inv_id, pinchedHomChainMap_id]
    inv_hom_id := by rw [← pinchedHomChainMap_comp, IsIso.inv_hom_id, pinchedHomChainMap_id] }
  exact e.isIso_hom

end SerrePositivity.InfinityCategories
