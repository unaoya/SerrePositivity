module
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # 主dg圏の充満dg部分圏

Hom複体・微分・豊穣合成をそのまま制限する。閉零射とH⁰の両方で包含は完全忠実。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : D → Prop)

/-- 対象の性質Pで制限した充満dg部分圏の対象型。対象宇宙は元のDから継承する。 -/
abbrev DGFullSubcategory := {x : D // P x}

/-- Hom複体・単位・合成を元の豊穣圏から制限し、その法則を継承する。 -/
instance dgFullSubcategoryEnrichment : DGCategory A (DGFullSubcategory D P) :=
  ofHomObjects A _ (fun x y => homObject A D x.val y.val)
    (fun x => eId (Complex A) x.val) (fun x y z => eComp (Complex A) x.val y.val z.val)
    (fun x y => EnrichedCategory.id_comp x.val y.val)
    (fun x y => EnrichedCategory.comp_id x.val y.val)
    (fun w x y z => EnrichedCategory.assoc w.val x.val y.val z.val)

/-- 充満dg部分圏の包含。各Hom複体上では恒等射である。 -/
def dgFullSubcategoryInclusion : DGFunctor A (DGFullSubcategory D P) D where
  obj x := x.val
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

/-- 包含は閉零射で充満。元と同じHom複体なので射をそのまま持ち上げる。 -/
instance dgFullSubcategoryInclusionClosedFull :
    (dgFullSubcategoryInclusion A D P).onClosed.Full where
  map_surjective {x y} f := by
    change ∃ g : 𝟙_ (Complex A) ⟶ homObject A D x.val y.val, g ≫ 𝟙 _ = f
    exact ⟨f, Category.comp_id _⟩

/-- 包含は閉零射で忠実。Hom複体上の恒等射との合成を消去する。 -/
instance dgFullSubcategoryInclusionClosedFaithful :
    (dgFullSubcategoryInclusion A D P).onClosed.Faithful where
  map_injective {x y} f g h := by
    let X : DGFullSubcategory D P := ForgetEnrichment.to (Complex A) x
    let Y : DGFullSubcategory D P := ForgetEnrichment.to (Complex A) y
    let f' : 𝟙_ (Complex A) ⟶ homObject A D X.val Y.val :=
      ForgetEnrichment.homTo (Complex A) f
    let g' : 𝟙_ (Complex A) ⟶ homObject A D X.val Y.val :=
      ForgetEnrichment.homTo (Complex A) g
    have h' : f' ≫ 𝟙 _ = g' ≫ 𝟙 _ := h
    have he : f' = g' := by simpa only [Category.comp_id] using h'
    exact he

/-- 包含は境界関係を反映する。同じHom複体上のホモトピーを使用する。 -/
lemma dgFullSubcategoryInclusion_boundary_iff {x y : ClosedCategory A (DGFullSubcategory D P)}
    (f g : x ⟶ y) :
    boundaryRelation A D ((dgFullSubcategoryInclusion A D P).onClosed.map f)
      ((dgFullSubcategoryInclusion A D P).onClosed.map g) ↔
        boundaryRelation A (DGFullSubcategory D P) f g := by
  change Nonempty (Homotopy (ForgetEnrichment.homTo (Complex A) f ≫ 𝟙 _)
    (ForgetEnrichment.homTo (Complex A) g ≫ 𝟙 _)) ↔
    Nonempty (Homotopy (ForgetEnrichment.homTo (Complex A) f)
      (ForgetEnrichment.homTo (Complex A) g))
  simp only [Category.comp_id]

/-- H⁰包含の射計算は閉零包含の商への像と一致する。 -/
lemma dgFullSubcategoryInclusion_onHomotopy_map
    {x y : ClosedCategory A (DGFullSubcategory D P)} (f : x ⟶ y) :
    (dgFullSubcategoryInclusion A D P).onHomotopy.map
        ((toHomotopy A (DGFullSubcategory D P)).map f) =
      (toHomotopy A D).map ((dgFullSubcategoryInclusion A D P).onClosed.map f) := rfl

/-- H⁰包含は充満。閉零射への商の全射性と閉零包含の充満性を使う。 -/
instance dgFullSubcategoryInclusionHomotopyFull :
    (dgFullSubcategoryInclusion A D P).onHomotopy.Full where
  map_surjective {x y} f := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
    obtain ⟨g, rfl⟩ := (dgFullSubcategoryInclusion A D P).onClosed.map_surjective f
    exact ⟨(toHomotopy A (DGFullSubcategory D P)).map g,
      dgFullSubcategoryInclusion_onHomotopy_map A D P g⟩

/-- H⁰包含は忠実。閉零代表で境界関係の反映に帰着する。 -/
instance dgFullSubcategoryInclusionHomotopyFaithful :
    (dgFullSubcategoryInclusion A D P).onHomotopy.Faithful where
  map_injective {x y} f g h := by
    obtain ⟨f, rfl⟩ := (toHomotopy A (DGFullSubcategory D P)).map_surjective f
    obtain ⟨g, rfl⟩ := (toHomotopy A (DGFullSubcategory D P)).map_surjective g
    rw [dgFullSubcategoryInclusion_onHomotopy_map,
      dgFullSubcategoryInclusion_onHomotopy_map] at h
    exact (toHomotopy_map_eq_iff A (DGFullSubcategory D P) f g).mpr
      ((dgFullSubcategoryInclusion_boundary_iff A D P f g).mp
        ((toHomotopy_map_eq_iff A D _ _).mp h))

end SerrePositivity.DifferentialGraded
