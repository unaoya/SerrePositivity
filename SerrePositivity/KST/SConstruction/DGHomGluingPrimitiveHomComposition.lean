module
public import SerrePositivity.KST.SConstruction.DGHomGluingPrimitiveComposition
public import SerrePositivity.KST.SConstruction.DGHomGluingActions

/-! # Hom 双加群 gluing の第三成分の通常順合成
概要：元の比較成分の合成を、元の標的内の二つの通常順合成に照合する。
方針：同じ双加群の左右作用を元の Hom 合成に戻し、次数符号をまとめる。
規約：第三成分を落とさない。使われ方：元の cone Hom 写像の合成保存。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

private lemma map_units {U V : ModuleCat R} (f : U ⟶ V) (r : ℤˣ) (z : U) :
    f (r • z) = r • f z := map_zsmul f.hom (r : ℤ) z

/-- 元の Hom gluing の通常順合成は同じ二 Hom 合成と後続次数の符号を回収する。 -/
lemma dgHomGluingPrimitive_comp {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Z).v
        (r + s) (r + s - 1) (by omega)
        (compose R (x := X) (y := Y) (z := Z) b a rfl) =
      compose R (x := p.obj X.left) (y := p.obj Y.left) (z := q.obj Z.right) (n := r + s - 1)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D _ Y Z).v s (s - 1) (by omega) b)
        ((p.map X.left Y.left).f r ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D _ X Y).f r a))
        (by omega) +
      s.negOnePow • compose R (x := p.obj X.left) (y := q.obj Y.right) (z := q.obj Z.right) (n :=
        r + s - 1)
        ((q.map Y.right Z.right).f s ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D _ Y Z).f s b))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D _ X Y).v r (r - 1) (by omega) a) (by omega) := by
  rw [compose]
  erw [map_units, dgHomGluingPrimitive_forward]
  erw [dgHomGluingBimodule_leftAction, dgHomGluingBimodule_rightAction]
  have hs : s.negOnePow * ((r - 1) * s).negOnePow = (r * s).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  have ht : (r * s).negOnePow * r.negOnePow = (r * (s - 1)).negOnePow := by
    rw [mul_sub, mul_one, Int.negOnePow_sub]
  let U : GradedHom R (p.obj X.left) (q.obj Z.right) (r + s - 1) :=
    forward R (x := p.obj X.left) (y := q.obj Y.right) (z := q.obj Z.right)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D _ X Y).v r (r - 1) (by omega) a)
      ((q.map Y.right Z.right).f s ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D _ Y Z).f s b)) (by omega)
  let V : GradedHom R (p.obj X.left) (q.obj Z.right) (r + s - 1) :=
    forward R (x := p.obj X.left) (y := p.obj Y.left) (z := q.obj Z.right)
      ((p.map X.left Y.left).f r ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D _ X Y).f r a))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D _ Y Z).v s (s - 1) (by omega) b) (by omega)
  change (r * s).negOnePow •
    (((r - 1) * s).negOnePow • (s * (r - 1)).negOnePow • U + r.negOnePow • V) =
    (r * (s - 1)).negOnePow • V + s.negOnePow • ((r - 1) * s).negOnePow • U
  simp only [smul_add, smul_smul, mul_comm s (r - 1),
    Int.units_mul_self, mul_one]
  rw [hs, ht]
  exact add_comm _ _

end SerrePositivity.KST.SConstruction
