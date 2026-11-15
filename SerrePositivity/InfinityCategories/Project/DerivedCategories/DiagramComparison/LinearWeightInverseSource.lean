module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeDiagramIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomSourceCochainEvaluation

/-!
概要：指定自由重み同型で戻すと、元の係数重み移送の逆射だけが残る。
方針：既存合成同型の両逆と閉零次始域射の前合成の結合則を使う。
規約：指定Moore・係数・点ごとの交換同型を保つ既存構成の合成則。
使われ方：HA 1.2.4、IS-W2 B02のA12の実始域移送とBK行合成則の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory HomologicalComplex CochainComplex HomComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable (W : J ⥤ SSet.{0})

/-- 元の自由重み同型と係数移送の逆射の合成では、同じ図式交換同型が消える。 -/
theorem freeLinearWeightDiagramIso_inverse_source :
    (freeLinearWeightDiagramIso A W).hom ≫ (normalizedLinearWeightDiagramIso A W).inv =
      (normalizedLinearWeightFreeIso A W.flip).inv := by
  simp only [normalizedLinearWeightDiagramIso, Iso.trans_inv, Iso.hom_inv_id_assoc]

/-- 同じ自由重み同型を前合成した全cochainでも、元の逆係数射と後続の始域射が残る。 -/
theorem freeLinearWeightDiagramIso_inverse_precomp
    {P Q : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (τ : (((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (Cochain.ofHom (freeLinearWeightDiagramIso A W).hom).comp
      ((Cochain.ofHom ((normalizedLinearWeightDiagramIso A W).inv ≫ τ)).comp z
        (zero_add p)) (zero_add p) =
      (Cochain.ofHom ((normalizedLinearWeightFreeIso A W.flip).inv ≫ τ)).comp z
        (zero_add p) := by
  rw [zeroSourcePrecomp_comp, ← Category.assoc, freeLinearWeightDiagramIso_inverse_source]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
