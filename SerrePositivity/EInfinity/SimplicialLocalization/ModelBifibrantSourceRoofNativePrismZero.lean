module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismZeroSlice
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrism
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Limits SSet MonoidalCategory SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial

private lemma uncurry_point_ext {S E : SSet.{u}} {p q : (Δ[0] : SSet.{u}) ⟶ E}
    (h : p = q) (f : S ⟶ sliceOver p) (g : S ⟶ sliceOver q)
    (hv : ∀ (n : ℕ) (a : S _⦋n⦌), (f.app (Opposite.op ⦋n⦌) a).val =
      (g.app (Opposite.op ⦋n⦌) a).val) : sliceOverUncurry f = sliceOverUncurry g := by
  subst q
  have he : f = g := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    exact Subtype.ext (hv n a)
  rw [he]

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNativePrism_zero_uncurry :
    sliceOverUncurry (prismEndpoint 0 _ ≫ modelBifibrantSourceRoofProductCommaNativePrism X Y q b) =
      (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv (Cocone.mk
        (modelBifibrantObject C Y)
        (modelBifibrantSourceRoofProductCommaRightLeg X Y q b))).val ≫
      hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) := by
  let P := RoofPrefix.prism (modelBifibrantRelativeCategory C)
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
    (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
    (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f)
  have hq := congrArg (fun z : (kanHammockNerve (modelBifibrantRelativeCategory C)) _⦋0⦌ =>
    SSet.yonedaEquiv.symm z)
    (hammockLocalizationNerveMap_vertex (modelBifibrantRelativeCategory C)
      (modelBifibrantObject C Y))
  refine (uncurry_point_ext hq
    (prismEndpoint 0 _ ≫ modelBifibrantSourceRoofProductCommaNativePrism X Y q b)
    (prismEndpoint 0 _ ≫ P) (fun _ _ => rfl)).trans ?_
  exact RoofPrefix.prism_zero_uncurry (modelBifibrantRelativeCategory C)
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
    (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
    (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNativePrism_zero_evaluation :
    (β_ (nerve (modelBifibrantSourceRoofProductComma X Y q b)) (Δ[1] : SSet.{max u v})).hom ≫
      rightMappingSpacePrism _ ≫ sliceOverUncurry
        (prismEndpoint 0 _ ≫ modelBifibrantSourceRoofProductCommaNativePrism X Y q b) =
    (modelBifibrantSourceRoofProductCommaRightHomotopy X Y q b).h := by
  rw [modelBifibrantSourceRoofProductCommaNativePrism_zero_uncurry X Y q b]
  have h := FrameHom.nerveCoconePrism_eq_natTrans
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (Cocone.mk (modelBifibrantObject C Y)
      (modelBifibrantSourceRoofProductCommaRightLeg X Y q b))
  exact (congrArg (fun f => f ≫
    hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) h)

end SerrePositivity.EInfinity.SimplicialLocalization
