module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeHomMap
public import SerrePositivity.KST.SConstruction.DGHomGluingConeComponentComposition
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeCompositionDegree

/-! # 元の実 cone Hom 写像の合成保存
概要：元の gluing の全次数合成を、同じ実 Perf cone の全 Hom 合成へ送る。
方針：三成分の合成公式と同じ実 end 内の cone 合成式を使う。
規約：第三成分を保持。使われ方：実 dg cone 関手の構成。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

private lemma map_units {U V : ModuleCat R} (f : U ⟶ V) (r : ℤˣ) (z : U) :
    f (r • z) = r • f z := map_zsmul f.hom (r : ℤ) z

/-- 同じ全 Hom 鎖写像は、元の通常順の全次数合成を保存する。 -/
lemma dgHomGluingConeHomMap_comp {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgHomGluingConeHomMap R C D E p q X Z).f (r + s)
        (compose R (x := X) (y := Y) (z := Z) b a rfl) =
      compose R (x := dgHomGluingTargetCone R C D E p q X)
        (y := dgHomGluingTargetCone R C D E p q Y)
        (z := dgHomGluingTargetCone R C D E p q Z)
        ((dgHomGluingConeHomMap R C D E p q Y Z).f s b)
        ((dgHomGluingConeHomMap R C D E p q X Y).f r a) rfl := by
  have hL := dgHomGluingConeLeftMap_comp R C D E p q X Y Z a b
  have hR := dgHomGluingConeRightMap_comp R C D E p q X Y Z a b
  have hH := dgHomGluingConePrimitive_comp R C D E p q X Y Z a b
  have he := congr (congrArg₂ (fun
      (u : (moduleHom R E (representable R (p.obj X.left))
        (representable R (p.obj Z.left))).X (r + s))
      (v : (moduleHom R E (representable R (q.obj X.right))
        (representable R (q.obj Z.right))).X (r + s)) => fun
      (h : (moduleHom R E (representable R (p.obj X.left))
        (representable R (q.obj Z.right))).X (r + s - 1)) =>
    dgGluingModuleConeElement R E
      (dgHomGluingTargetModuleMap R C D E p q X)
      (dgHomGluingTargetModuleMap R C D E p q Z) u v h (by omega)) hL hR) hH
  have hc := dgGluingModuleConeElement_comp_at R E
    (dgHomGluingTargetModuleMap R C D E p q X)
    (dgHomGluingTargetModuleMap R C D E p q Y)
    (dgHomGluingTargetModuleMap R C D E p q Z)
    (n := r) (m := r - 1) (p := s) (l := s - 1) (o := r + s - 1)
    ((dgHomGluingConeLeftMap R C D E p q X Y).f r a)
    ((dgHomGluingConeRightMap R C D E p q X Y).f r a)
    ((dgHomGluingConePrimitive R C D E p q X Y).v r (r - 1) (by omega) a) (by omega)
    ((dgHomGluingConeLeftMap R C D E p q Y Z).f s b)
    ((dgHomGluingConeRightMap R C D E p q Y Z).f s b)
    ((dgHomGluingConePrimitive R C D E p q Y Z).v s (s - 1) (by omega) b)
    (by omega) (by omega)
  exact he.trans hc.symm

/-- 同じ全 Hom 鎖写像は、元の豊穣順合成も全次数で保存する。 -/
lemma dgHomGluingConeHomMap_forward {r s n : ℤ} (hn : r + s = n)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgHomGluingConeHomMap R C D E p q X Z).f n
        (forward R (x := X) (y := Y) (z := Z) a b hn) =
      forward R (x := dgHomGluingTargetCone R C D E p q X)
        (y := dgHomGluingTargetCone R C D E p q Y)
        (z := dgHomGluingTargetCone R C D E p q Z)
        ((dgHomGluingConeHomMap R C D E p q X Y).f r a)
        ((dgHomGluingConeHomMap R C D E p q Y Z).f s b) hn := by
  cases hn
  rw [forward_eq_signed_compose, forward_eq_signed_compose]
  erw [map_units, dgHomGluingConeHomMap_comp]

end SerrePositivity.KST.SConstruction
