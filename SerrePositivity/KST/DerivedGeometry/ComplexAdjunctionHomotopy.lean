module

public import SerrePositivity.KST.DerivedGeometry.ComplexAdjunction
public import Mathlib.Algebra.Homology.Homotopy

/-!
概要：加法的随伴の複体の Hom 同値はホモトピーを保つ。
方針：各成分の随伴の加法性と左右自然性でホモトピーの等式を移す。
規約：任意の複体形状。有界性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の非有界 K-injective 比較の接続点。
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
概要：左随伴の像からの鎖写像のホモトピーを右随伴へのホモトピーへ移す。
方針：ホモトピーの各成分を元の Hom 同値で写す。
規約：微分の式は元の随伴の自然性で証明する。
使われ方：TT §3、Toën §3.2 の K-injective 性の移送。
-/
def adjunctionComplexHomotopy {K : HomologicalComplex C c} {L : HomologicalComplex D c}
    {f g : (F.mapHomologicalComplex c).obj K ⟶ L} (h : Homotopy f g) :
    Homotopy (adjunctionComplexHomEquiv adj c K L f) (adjunctionComplexHomEquiv adj c K L g) where
  hom i j := (adj.homEquiv _ _) (h.hom i j)
  zero i j hij := by rw [h.zero i j hij, adj.homAddEquiv_zero]
  comm i := by
    change (adj.homEquiv _ _) (f.f i) =
      K.d i (c.next i) ≫ (adj.homEquiv _ _) (h.hom (c.next i) i) +
        (adj.homEquiv _ _) (h.hom i (c.prev i)) ≫ G.map (L.d (c.prev i) i) +
        (adj.homEquiv _ _) (g.f i)
    simpa only [dNext, prevD,
      AddMonoidHom.mk'_apply, Functor.mapHomologicalComplex_obj_d,
      adj.homAddEquiv_add, adj.homEquiv_naturality_left, adj.homEquiv_naturality_right] using
      congrArg (adj.homEquiv (K.X i) (L.X i)) (h.comm i)

/--
概要：右随伴への鎖写像のホモトピーを左随伴の像からのホモトピーへ戻す。
方針：各成分で Hom 同値の逆の加法性と自然性を使う。
規約：任意の複体形状、有界性不要。
使われ方：TT §3、Toën §3.2 の非有界ホモトピー圏上の随伴。
-/
def adjunctionComplexHomotopySymm {K : HomologicalComplex C c} {L : HomologicalComplex D c}
    {f g : K ⟶ (G.mapHomologicalComplex c).obj L} (h : Homotopy f g) :
    Homotopy ((adjunctionComplexHomEquiv adj c K L).symm f)
      ((adjunctionComplexHomEquiv adj c K L).symm g) where
  hom i j := (adj.homEquiv _ _).symm (h.hom i j)
  zero i j hij := by rw [h.zero i j hij, adj.homAddEquiv_symm_zero]
  comm i := by
    change (adj.homEquiv _ _).symm (f.f i) =
      F.map (K.d i (c.next i)) ≫ (adj.homEquiv _ _).symm (h.hom (c.next i) i) +
        (adj.homEquiv _ _).symm (h.hom i (c.prev i)) ≫ L.d (c.prev i) i +
        (adj.homEquiv _ _).symm (g.f i)
    have hh := congrArg (adj.homEquiv (K.X i) (L.X i)).symm (h.comm i)
    simp only [dNext, prevD, AddMonoidHom.mk'_apply, Functor.mapHomologicalComplex_obj_d,
      adj.homAddEquiv_symm_add] at hh
    rw [adj.homEquiv_naturality_right_symm (h.hom i (c.prev i)) (L.d (c.prev i) i)] at hh
    rw [adj.homEquiv_naturality_left_symm (K.d i (c.next i)) (h.hom (c.next i) i)] at hh
    exact hh

end SerrePositivity.KST.DerivedGeometry
