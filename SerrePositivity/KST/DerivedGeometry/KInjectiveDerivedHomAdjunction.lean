module

public import SerrePositivity.KST.DerivedGeometry.AdjunctionKInjective
public import SerrePositivity.KST.DerivedGeometry.HomotopyAdjunctionHomEquiv
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
概要：完全左随伴の非有界導来 Hom を右随伴の K-injective 模型と比較する。
方針：ホモトピー類の随伴と K-injective 対象への導来局所化の全単射を合成する。
規約：分解の存在は入力しない。指定された実際の K-injective 複体上の計算。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の非有界アフィン比較の Hom 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F] (adj : F ⊣ G)

/--
概要：K-injective な終域に対する局所化後の Hom は非有界の随伴で比較できる。
方針：両側の K-injective 性でホモトピー類から導来 Hom への全単射を使う。
規約：始域に次数の上限・下限は要求しない。
使われ方：TT §3、Toën §3.2 の非有界右導来 Hom の計算。
-/
def kInjectiveDerivedHomAdjunction (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    [L.IsKInjective] :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶ DerivedCategory.Q.obj L) ≃
    (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) := by
  have : CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L) :=
    rightAdjoint_map_isKInjective adj L
  let eD := Equiv.ofBijective (DerivedCategory.Qh.map :
    ((HomotopyCategory.quotient D (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (HomotopyCategory.quotient D (.up ℤ)).obj L) → _)
    (CochainComplex.IsKInjective.Qh_map_bijective _ L)
  let eC := Equiv.ofBijective (DerivedCategory.Qh.map :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) → _)
    (CochainComplex.IsKInjective.Qh_map_bijective _ _)
  exact (Iso.homCongr ((DerivedCategory.quotientCompQhIso D).symm.app _)
      ((DerivedCategory.quotientCompQhIso D).symm.app L)).trans
    (eD.symm.trans ((homotopyAdjunctionHomEquiv adj (.up ℤ) K L).trans
      (eC.trans (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
        ((DerivedCategory.quotientCompQhIso C).app _)))))

end SerrePositivity.KST.DerivedGeometry
