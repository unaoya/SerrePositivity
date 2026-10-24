module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyFamilyNaturality
public import SerrePositivity.InfinityCategories.F1B.Adjunction.PointwiseUnitComparison

/-!
概要：指定単位の標準写像空間比較を、元の左右輸送の比較へ接続する。
方針：右輸送の自然性と同じ単位成分の合成式を任意の区間族で照合し、同値性を移す。
規約：合成式と左右比較の同値性は別途証明する。使われ方：Quillen 導来単位の認識。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
/-- 元の関手の合成は、区間写像空間への作用の合成と厳密に一致する。 -/
lemma intervalFunctorMap_comp {X Y Z : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ Z)
    (x y : X _⦋0⦌) :
    intervalFunctorMap F x y ≫ intervalFunctorMap G
        (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) =
      intervalFunctorMap (F ≫ G) x y := by
  apply intervalMappingUncurry_injective
  have hl := intervalFunctorMap_uncurry (intervalFunctorMap F x y) G
  have hr := intervalFunctorMap_uncurry (𝟙 (intervalMappingSpace x y)) (F ≫ G)
  have hm := intervalFunctorMap_uncurry (𝟙 (intervalMappingSpace x y)) F
  simp only [Category.id_comp] at hr hm
  rw [hl, hm, hr]
  rfl
/-- 標準の前合成を関手で写した族は、元の射の像による前合成を表す。 -/
lemma intervalPrecompose_postcomp_family {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    {a b c : X _⦋0⦌}
    (e : (HomotopyCategory.mk a : hoFunctor.obj X) ⟶ HomotopyCategory.mk b)
    (f : A ⟶ intervalMappingSpace b c) :
    intervalFamilyHom (f ≫ intervalPrecompose c e ≫ intervalFunctorMap F a c) =
      constantFunctorHomMap A ((hoFunctor.map F).toFunctor.map e) ≫
        intervalFamilyHom (f ≫ intervalFunctorMap F b c) := by
  rw [← Category.assoc, intervalFunctorMap_familyHom, intervalPrecompose_family,
    CategoryTheory.Functor.map_comp]
  rw [← constantFunctorHomMap_postcomp A F e]
  rw [intervalFunctorMap_familyHom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
/-- 指定単位の標準比較を混合写像空間へ写した族の合成式。 -/
lemma unitIntervalMap_collage_family {A X Y E : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory E]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (i : X ⟶ E) (j : Y ⟶ E) (H : SSet.Homotopy (G ≫ i) j)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (lx : (HomotopyCategory.mk (i.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj E) ⟶
      HomotopyCategory.mk (j.app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) x)))
    (hc : (hoFunctor.map i).toFunctor.map (qcatUnitComponent η x) ≫
      functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy H)) (F.app (Opposite.op ⦋0⦌) x) = lx)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    intervalFamilyHom (f ≫ unitIntervalMap η x y ≫
      intervalFunctorMap i x (G.app (Opposite.op ⦋0⦌) y) ≫
      intervalPostcompose (i.app (Opposite.op ⦋0⦌) x)
        (functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy H)) y)) =
      constantFunctorHomMap A lx ≫ intervalFamilyHom
        (f ≫ intervalFunctorMap j (F.app (Opposite.op ⦋0⦌) x) y) := by
  change intervalFamilyHom (((f ≫ intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) y) ≫
    intervalPrecompose (G.app (Opposite.op ⦋0⦌) y) (qcatUnitComponent η x) ≫
    intervalFunctorMap i x (G.app (Opposite.op ⦋0⦌) y)) ≫
    intervalPostcompose (i.app (Opposite.op ⦋0⦌) x) _) = _
  rw [intervalPostcompose_family, intervalPrecompose_postcomp_family]
  simp only [Category.assoc, intervalFunctorMap_comp]
  rw [homotopyFamily_composition H f]
  rw [← Category.assoc, ← constantFunctorHomMap_comp, hc]

/-- 指定単位の標準比較は、輸送の比較式が与える元の左の前合成とホモトピック。 -/
lemma unitIntervalMap_collage_homotopy {X Y E : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory E]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (i : X ⟶ E) (j : Y ⟶ E) (H : SSet.Homotopy (G ≫ i) j)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (lx : (HomotopyCategory.mk (i.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj E) ⟶
      HomotopyCategory.mk (j.app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) x)))
    (hc : (hoFunctor.map i).toFunctor.map (qcatUnitComponent η x) ≫
      functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy H)) (F.app (Opposite.op ⦋0⦌) x) = lx) :
    Nonempty (SSet.Homotopy
      (unitIntervalMap η x y ≫ intervalFunctorMap i x (G.app (Opposite.op ⦋0⦌) y) ≫
        intervalPostcompose (i.app (Opposite.op ⦋0⦌) x)
          (functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
            (functorEdgeOfSimplicialHomotopy H)) y))
      (intervalFunctorMap j (F.app (Opposite.op ⦋0⦌) x) y ≫
        intervalPrecompose (j.app (Opposite.op ⦋0⦌) y) lx)) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalPrecompose_family]
  simpa only [Category.id_comp] using unitIntervalMap_collage_family η i j H x y lx hc
    (𝟙 (intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y))

/-- 左右の元の比較写像の同値性と輸送の比較式から、指定単位の標準比較の同値性を得る。 -/
lemma unitIntervalMap_isSimplicialHomotopyEquivalence_of_collage {X Y E : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory E]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (i : X ⟶ E) (j : Y ⟶ E) (H : SSet.Homotopy (G ≫ i) j)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (lx : (HomotopyCategory.mk (i.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj E) ⟶
      HomotopyCategory.mk (j.app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) x)))
    (hc : (hoFunctor.map i).toFunctor.map (qcatUnitComponent η x) ≫
      functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy H)) (F.app (Opposite.op ⦋0⦌) x) = lx)
    (hleft : IsSimplicialHomotopyEquivalence
      (intervalFunctorMap j (F.app (Opposite.op ⦋0⦌) x) y ≫
        intervalPrecompose (j.app (Opposite.op ⦋0⦌) y) lx))
    (hright : IsSimplicialHomotopyEquivalence
      (intervalFunctorMap i x (G.app (Opposite.op ⦋0⦌) y) ≫
        intervalPostcompose (i.app (Opposite.op ⦋0⦌) x)
          (functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
            (functorEdgeOfSimplicialHomotopy H)) y))) :
    IsSimplicialHomotopyEquivalence (unitIntervalMap η x y) := by
  obtain ⟨W⟩ := unitIntervalMap_collage_homotopy η i j H x y lx hc
  have hw := hleft.isQCatEquivalence.ofFunctorIso
    (functorIsoOfSimplicialHomotopy W).symm
  exact (hright.isQCatEquivalence.cancel_right hw).isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
