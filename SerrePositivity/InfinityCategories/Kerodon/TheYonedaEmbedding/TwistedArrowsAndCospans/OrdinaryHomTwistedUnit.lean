module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedReadPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedReadReindex

/-!
概要：通常の Hom の元の圏から twisted arrow へ写して読み戻すと元の全射列に戻る。
方針：各対象は零次の単位と全再添字で比較し、射は検証済みの両端射影で比較する。
規約：対象だけの逆関係で止めず、全対象・全射を持つ関手の等式を示す。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の Hom 模型比較の単位。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {n : ℕ}

/-- 指定比較の読み戻しは各対象の同じ射に戻る。
Kerodon Proposition 8.1.1.10（Tag 03JN）、全対象の単位則。 -/
lemma ordinaryHomTwistedRead_obj_simplex
    (s : ComposableArrows (OrdinaryHomElements C) n) (i : Fin (n + 1)) :
    (ordinaryHomTwistedRead (ordinaryHomTwistedSimplex s)).obj i = s.obj i := by
  let α : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom (OrderHom.const (Fin 1) i)
  have hs : α.toOrderHom.toFunctor ⋙ s = ComposableArrows.mk₀ (s.obj i) :=
    ComposableArrows.ext₀ rfl
  have hh := ordinaryHomTwistedRead_obj_reindex (ordinaryHomTwistedSimplex s) α 0
  rw [ordinaryHomTwistedSimplex_naturality, hs, ordinaryHomTwistedRead_point] at hh
  exact hh.symm

private lemma elementsHom_hext {x y x' y' : OrdinaryHomElements C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) (g : x' ⟶ y')
    (h₁ : HEq f.hom.1 g.hom.1) (h₂ : HEq f.hom.2 g.hom.2) : HEq f g := by
  subst x' y'
  exact heq_of_eq (Functor.Elements.hom_ext (_root_.Prod.ext (eq_of_heq h₁) (eq_of_heq h₂)))

/-- 元の Hom の全射列は、指定 twisted arrow 比較と読み戻しの往復で変わらない。
Kerodon Proposition 8.1.1.10（Tag 03JN）、射を含む全単体の単位則。 -/
lemma ordinaryHomTwistedRead_simplex (s : ComposableArrows (OrdinaryHomElements C) n) :
    ordinaryHomTwistedRead (ordinaryHomTwistedSimplex s) = s := by
  have hs : ordinaryHomTwistedRead (ordinaryHomTwistedSimplex s) ⋙
      ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.fst Cᵒᵖ C =
      s ⋙ ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.fst Cᵒᵖ C := by
    rw [ordinaryHomTwistedRead_source]
    exact congrArg (fun q : nerve (OrdinaryHomElements C) ⟶ nerve Cᵒᵖ =>
      q.app (Opposite.op ⦋n⦌) s) (ordinaryHomTwistedComparison_left (C := C))
  have ht : ordinaryHomTwistedRead (ordinaryHomTwistedSimplex s) ⋙
      ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.snd Cᵒᵖ C =
      s ⋙ ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.snd Cᵒᵖ C := by
    rw [ordinaryHomTwistedRead_target]
    exact congrArg (fun q : nerve (OrdinaryHomElements C) ⟶ nerve C =>
      q.app (Opposite.op ⦋n⦌) s) (ordinaryHomTwistedComparison_right (C := C))
  refine CategoryTheory.Functor.hext (ordinaryHomTwistedRead_obj_simplex s) ?_
  intro i j h
  exact elementsHom_hext (ordinaryHomTwistedRead_obj_simplex s i)
    (ordinaryHomTwistedRead_obj_simplex s j) _ _
    (CategoryTheory.Functor.hcongr_hom hs h) (CategoryTheory.Functor.hcongr_hom ht h)

/-- 指定 Hom 比較は各次数で単射である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、検証済みの単位則の帰結。 -/
lemma ordinaryHomTwistedComparison_injective (n : ℕ) :
    Function.Injective ((ordinaryHomTwistedComparison C).app (Opposite.op ⦋n⦌)) := by
  intro s t h
  have hh := congrArg ordinaryHomTwistedRead h
  exact (ordinaryHomTwistedRead_simplex s).symm.trans
    (hh.trans (ordinaryHomTwistedRead_simplex t))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
