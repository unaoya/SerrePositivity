module
public import SerrePositivity.KST.SConstruction.DGHomGluingPrimitiveHomComposition
public import SerrePositivity.KST.SConstruction.DGHomGluingConePrimitiveDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaGradedUnits

/-! # 実 cone Hom の元の三成分の合成保存
概要：左右鎖写像と第三比較が元の gluing の通常順合成をどう写すかを照合する。
方針：元の射影・Yoneda の dg 関手法則と元の第三成分の合成式を使う。
規約：第三比較と次数符号を保持。使われ方：実 cone dg 関手の合成法則。
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

/-- 元の左 Hom 成分は全次数の通常順合成を保存する。 -/
lemma dgHomGluingConeLeftMap_comp {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgHomGluingConeLeftMap R C D E p q X Z).f (r + s)
        (compose R (x := X) (y := Y) (z := Z) b a rfl) =
      compose R (x := representable R (p.obj X.left))
        (y := representable R (p.obj Y.left)) (z := representable R (p.obj Z.left))
        ((dgHomGluingConeLeftMap R C D E p q Y Z).f s b)
        ((dgHomGluingConeLeftMap R C D E p q X Y).f r a) rfl :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctor_map_compose R
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp p).comp
      (dgYoneda R E)) b a rfl

/-- 元の右 Hom 成分も、同じ元の右射影を介して全次数合成を保存する。 -/
lemma dgHomGluingConeRightMap_comp {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgHomGluingConeRightMap R C D E p q X Z).f (r + s)
        (compose R (x := X) (y := Y) (z := Z) b a rfl) =
      compose R (x := representable R (q.obj X.right))
        (y := representable R (q.obj Y.right)) (z := representable R (q.obj Z.right))
        ((dgHomGluingConeRightMap R C D E p q Y Z).f s b)
        ((dgHomGluingConeRightMap R C D E p q X Y).f r a) rfl := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctor_map_compose R
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)).comp q).comp
      (dgYoneda R E)) b a rfl
  change ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)).map X Z ≫
    q.map X.right Z.right) ≫ (dgYoneda R E).map _ _).f (r + s)
      (compose R (x := X) (y := Y) (z := Z) b a rfl)) =
    compose R (x := representable R (q.obj X.right))
      (y := representable R (q.obj Y.right)) (z := representable R (q.obj Z.right))
      ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)).map Y Z ≫
        q.map Y.right Z.right) ≫ (dgYoneda R E).map _ _).f s b)
      ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)).map X Y ≫
        q.map X.right Y.right) ≫ (dgYoneda R E).map _ _).f r a) rfl at hc
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map] at hc
  exact hc

/-- 第三比較は元の二 Hom 合成と後続次数の符号を保持する。 -/
lemma dgHomGluingConePrimitive_comp {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgHomGluingConePrimitive R C D E p q X Z).v (r + s) (r + s - 1) (by omega)
        (compose R (x := X) (y := Y) (z := Z) b a rfl) =
      compose R (x := representable R (p.obj X.left))
        (y := representable R (p.obj Y.left)) (z := representable R (q.obj Z.right)) (n := r + s -
          1)
        ((dgHomGluingConePrimitive R C D E p q Y Z).v s (s - 1) (by omega) b)
        ((dgHomGluingConeLeftMap R C D E p q X Y).f r a) (by omega) +
      s.negOnePow • compose R (x := representable R (p.obj X.left))
        (y := representable R (q.obj Y.right)) (z := representable R (q.obj Z.right)) (n := r + s
          - 1)
        ((dgHomGluingConeRightMap R C D E p q Y Z).f s b)
        ((dgHomGluingConePrimitive R C D E p q X Y).v r (r - 1) (by omega) a) (by omega) := by
  simp only [dgHomGluingConePrimitive_apply]
  erw [dgHomGluingPrimitive_comp, map_add]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctor_map_compose R (dgYoneda R E)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D _ Y Z).v s (s - 1) (by omega) b)
    ((p.map X.left Y.left).f r ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D _ X Y).f r a))
    (by omega : r + (s - 1) = r + s - 1)]
  erw [map_units (R := R)
    (((dgYoneda R E).map (p.obj X.left) (q.obj Z.right)).f (r + s - 1)) s.negOnePow
    (compose R (x := p.obj X.left) (y := q.obj Y.right) (z := q.obj Z.right)
      (n := r + s - 1)
      ((q.map Y.right Z.right).f s ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D _ Y Z).f s b))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D _ X Y).v r (r - 1) (by omega) a) (by omega))]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctor_map_compose R (dgYoneda R E)
    ((q.map Y.right Z.right).f s ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D _ Y Z).f s b))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D _ X Y).v r (r - 1) (by omega) a)
    (by omega : r - 1 + s = r + s - 1)]
  rfl

end SerrePositivity.KST.SConstruction
