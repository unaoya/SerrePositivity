module

public import SerrePositivity.KST.DerivedGeometry.ComplexAdjunctionHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
概要：加法的随伴は任意の複体形状のホモトピー類の Hom 同値を与える。
方針：鎖写像の Hom 同値が両方向にホモトピーを保つことから商へ降ろす。
規約：有界性・分解の存在を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の非有界 K-injective 模型の Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
  {ι : Type*} (c : ComplexShape ι)

/--
概要：左随伴と右随伴の鎖写像の随伴はホモトピー類の同値へ降りる。
方針：Hom の商で両方向を定義し、元の Hom 同値の逆性を使う。
規約：実際の Mathlib のホモトピー圏の射を比較する。
使われ方：TT §3、Toën §3.2 の非有界導来 Hom 比較。
-/
def homotopyAdjunctionHomEquiv (K : HomologicalComplex C c) (L : HomologicalComplex D c) :
    ((HomotopyCategory.quotient D c).obj ((F.mapHomologicalComplex c).obj K) ⟶
      (HomotopyCategory.quotient D c).obj L) ≃
    ((HomotopyCategory.quotient C c).obj K ⟶
      (HomotopyCategory.quotient C c).obj ((G.mapHomologicalComplex c).obj L)) where
  toFun := Quot.lift
    (fun f => (HomotopyCategory.quotient C c).map (adjunctionComplexHomEquiv adj c K L f))
    (fun f g h => HomotopyCategory.eq_of_homotopy _ _ (adjunctionComplexHomotopy adj c
      ((HomRel.compClosure_iff_self (homotopic D c) f g).mp h).some))
  invFun := Quot.lift
    (fun f => (HomotopyCategory.quotient D c).map ((adjunctionComplexHomEquiv adj c K L).symm f))
    (fun f g h => HomotopyCategory.eq_of_homotopy _ _ (adjunctionComplexHomotopySymm adj c
      ((HomRel.compClosure_iff_self (homotopic C c) f g).mp h).some))
  left_inv f := by
    refine Quot.inductionOn f (fun f => ?_)
    change (HomotopyCategory.quotient D c).map
      ((adjunctionComplexHomEquiv adj c K L).symm (adjunctionComplexHomEquiv adj c K L f)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv f := by
    refine Quot.inductionOn f (fun f => ?_)
    change (HomotopyCategory.quotient C c).map
      (adjunctionComplexHomEquiv adj c K L ((adjunctionComplexHomEquiv adj c K L).symm f)) = _
    rw [Equiv.apply_symm_apply]
    rfl

end SerrePositivity.KST.DerivedGeometry
