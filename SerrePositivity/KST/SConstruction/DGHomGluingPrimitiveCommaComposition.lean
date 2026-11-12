module
public import SerrePositivity.KST.SConstruction.DGHomGluingCommaComponents
public import SerrePositivity.KST.SConstruction.DGHomGluingYonedaComposition
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # 元の gluing 第三成分の全次数合成
概要：元の gluing の実合成の第三成分を、同じ双加群の二作用に戻す。
方針：既存 comma 合成式を同じ Yoneda 同型とその逆像の評価で移す。
規約：全次数の Koszul 符号を保持。使われ方：実 cone Hom の合成保存。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

private lemma map_units {U V : ModuleCat R} (f : U ⟶ V) (r : ℤˣ) (z : U) :
    f (r • z) = r • f z := map_zsmul f.hom (r : ℤ) z

/-- 元の豊穣合成の第三成分を、同じ comma の二項へ戻した実等式。 -/
lemma dgHomGluingPrimitive_forward_comma {p q : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X q)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M Y Z).X p) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Z).v (q + p) (q + p - 1) (by omega)
        (forward R (x := X) (y := Y) (z := Z) a b rfl) =
      (dgYonedaIso R X.left (M.rightAt Z.right)).hom.f (q + p - 1)
        (forward R (x := representable R X.left) (y := M.rightAt Y.right)
          (z := M.rightAt Z.right)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).v
            q (q - 1) (by omega) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f q a))
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R D (RightModule R C) M.toFunctor
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)).f p
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M Y Z).hom.f p b)) (by omega)) +
      q.negOnePow • (dgYonedaIso R X.left (M.rightAt Z.right)).hom.f (q + p - 1)
        (forward R (x := representable R X.left) (y := representable R Y.left)
          (z := M.rightAt Z.right)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).f q
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f q a))
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)).v
            p (p - 1) (by omega) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M Y Z).hom.f p b))
          (by omega)) := by
  rw [dgHomGluingPrimitive_recover]
  have hf := DGFunctor.map_forward R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) a b rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Z).hom.f (q + p)
    (forward R (x := X) (y := Y) (z := Z) a b rfl) = _ at hf
  erw [hf, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaForward_primitive]
  erw [map_add, map_units]
  rfl

end SerrePositivity.KST.SConstruction
