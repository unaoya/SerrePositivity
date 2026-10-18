module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
概要：加法的随伴の複体および bounded below 複体への持ち上げ。
方針：各次数の Hom 同値を微分と両立させ、元の随伴の自然性を使う。
規約：導来局所化前の実際の鎖写像の同値を証明する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' t
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
  {ι : Type t} (c : ComplexShape ι)

/--
概要：加法的随伴は任意の複体形状の鎖写像の Hom 同値を与える。
方針：各次数の随伴の Hom 同値に左・右自然性を適用して微分との可換性を示す。
規約：各次数の写像を同じ随伴で計算する。
使われ方：TT §3、Toën §3.2 の複体上の随伴。
-/
def adjunctionComplexHomEquiv (K : HomologicalComplex C c) (L : HomologicalComplex D c) :
    ((F.mapHomologicalComplex c).obj K ⟶ L) ≃ (K ⟶ (G.mapHomologicalComplex c).obj L) where
  toFun f :=
    { f := fun i => (adj.homEquiv _ _) (f.f i)
      comm' i j _ :=
        (adj.homEquiv_naturality_right (f.f i) (L.d i j)).symm.trans
          ((congrArg (adj.homEquiv (K.X i) (L.X j)) (f.comm i j)).trans
            (adj.homEquiv_naturality_left (K.d i j) (f.f j))) }
  invFun f :=
    { f := fun i => (adj.homEquiv _ _).symm (f.f i)
      comm' i j _ :=
        (adj.homEquiv_naturality_right_symm (f.f i) (L.d i j)).symm.trans
          ((congrArg (adj.homEquiv (K.X i) (L.X j)).symm (f.comm i j)).trans
            (adj.homEquiv_naturality_left_symm (K.d i j) (f.f j))) }
  left_inv f := by ext i; exact (adj.homEquiv _ _).symm_apply_apply _
  right_inv f := by ext i; exact (adj.homEquiv _ _).apply_symm_apply _

variable [HasZeroObject C] [HasZeroObject D]

/--
概要：bounded below 複体における加法的随伴の Hom 同値。
方針：実際の鎖写像の同値を充満部分圏の射へ束ねる。
規約：複体の下限は元の対象のものを保持する。
使われ方：TT §3・§8、Toën §3.2 の bounded below 導来随伴。
-/
def adjunctionComplexPlusHomEquiv (K : CochainComplex.Plus C) (L : CochainComplex.Plus D) :
    (F.mapCochainComplexPlus.obj K ⟶ L) ≃ (K ⟶ G.mapCochainComplexPlus.obj L) where
  toFun f := ObjectProperty.homMk (adjunctionComplexHomEquiv adj (.up ℤ) K.obj L.obj f.hom)
  invFun f := ObjectProperty.homMk ((adjunctionComplexHomEquiv adj (.up ℤ) K.obj L.obj).symm f.hom)
  left_inv f := by
    apply ObjectProperty.hom_ext
    exact (adjunctionComplexHomEquiv adj (.up ℤ) K.obj L.obj).symm_apply_apply f.hom
  right_inv f := by
    apply ObjectProperty.hom_ext
    exact (adjunctionComplexHomEquiv adj (.up ℤ) K.obj L.obj).apply_symm_apply f.hom

/--
概要：加法的随伴は bounded below 複体の圏の随伴に持ち上がる。
方針：鎖写像の各成分で元の Hom 同値の両側自然性を使う。
規約：局所化や導来比較はまだ用いない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の導来随伴の入力。
-/
def adjunctionComplexPlus : F.mapCochainComplexPlus ⊣ G.mapCochainComplexPlus :=
  Adjunction.mkOfHomEquiv
    { homEquiv := adjunctionComplexPlusHomEquiv adj
      homEquiv_naturality_left_symm := by
        intro K K' L f g
        apply ObjectProperty.hom_ext
        ext i
        exact adj.homEquiv_naturality_left_symm (f.hom.f i) (g.hom.f i)
      homEquiv_naturality_right := by
        intro K L L' f g
        apply ObjectProperty.hom_ext
        ext i
        exact adj.homEquiv_naturality_right (f.hom.f i) (g.hom.f i) }

end SerrePositivity.KST.DerivedGeometry
