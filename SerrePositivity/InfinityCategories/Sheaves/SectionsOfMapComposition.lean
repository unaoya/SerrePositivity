module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.SectionsOf
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SectionsConeMapComposition
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SectionsMapConeProjection
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SectionsRestrictionProjection

/-!
概要：指定された三つの切断の極限錐で、制限の合成を計算する。
方針：切断錐の普遍辺の合成を頂点射影へ送り、始点の等式をそろえる。
規約：HTT §1.2.13 と §6.2.2 の切断錐の計算。元の三つの極限錐を保持する。
使われ方：5∞-1 の R09.1。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Sheaves

private lemma map_four_comp {A B : Type u} [Category.{u} A] [Category.{u} B]
    (F : A ⥤ B) {a b c d e : A} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) :
    F.map f ≫ F.map g ≫ F.map h ≫ F.map k = F.map (f ≫ g ≫ h ≫ k) := by
  simp only [Functor.map_comp]

private lemma eqToHom_three {A : Type u} [Category.{u} A] {a b c d : A}
    (h : a = b) (k : b = c) (l : c = d) (r : a = d) :
    eqToHom h ≫ eqToHom k ≫ eqToHom l = eqToHom r := by
  rw [← Category.assoc, eqToHom_trans, eqToHom_trans]

private lemma projection_comp_calculation {A : Type u} [Category.{u} A]
    {a b c d e f g h : A} (s : a ⟶ b) (l : b ⟶ c) (x : c ⟶ d)
    (m : d ⟶ g) (y : g ⟶ h) (z₀ : c ⟶ e) (z₁ : d ⟶ f) (u₁ : f ⟶ g)
    (w : a ⟶ e) (v : e ⟶ f) (k : b ⟶ h)
    (hk : l ≫ x ≫ m ≫ y = k) (hm : m = z₁ ≫ u₁)
    (hx : x ≫ z₁ = z₀ ≫ v) (hw : s ≫ l ≫ z₀ = w) :
    s ≫ k = (w ≫ v) ≫ (u₁ ≫ y) := by
  calc
    s ≫ k = s ≫ l ≫ x ≫ m ≫ y := congrArg (fun j => s ≫ j) hk.symm
    _ = s ≫ l ≫ (x ≫ z₁) ≫ u₁ ≫ y := by rw [hm]; simp only [Category.assoc]
    _ = (s ≫ l ≫ z₀) ≫ v ≫ u₁ ≫ y := by rw [hx]; simp only [Category.assoc]
    _ = _ := by rw [hw]; simp only [Category.assoc]

private lemma projection_naturality {A B D : Type u} [Category.{u} A] [Category.{u} B]
    [Category.{u} D] (F : A ⥤ B) (π : B ⥤ D) (ρ : A ⥤ D) (h : F ⋙ π = ρ)
    {x y : A} (b : x ⟶ y)
    (ex : π.obj (F.obj x) = ρ.obj x) (ey : π.obj (F.obj y) = ρ.obj y) :
    π.map (F.map b) ≫ eqToHom ey = eqToHom ex ≫ ρ.map b := by
  simpa only [eqToHom_app, Functor.comp_map] using (eqToHom h).naturality b

private def normalizedSectionsProjection {I : Type u} [SmallCategory I]
    {P Q : I ⥤ Type u} {E : SSet.{u + 1}} [Quasicategory E]
    (f : P ⟶ Q) (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (cP : JoinCone (SetWeight.diagram P O)) (cQ : JoinCone (SetWeight.diagram Q O))
    (a : (HomotopyCategory.mk (SetWeight.restrictSectionsCone f O cQ) :
      hoFunctor.obj (sliceOver (SetWeight.diagram P O))) ⟶ HomotopyCategory.mk cP) :
    (HomotopyCategory.mk cQ.vertex : hoFunctor.obj E) ⟶ HomotopyCategory.mk cP.vertex :=
  eqToHom (congrArg HomotopyCategory.mk (SetWeight.restrictSectionsCone_vertex f O cQ).symm) ≫
    (hoFunctor.map (sliceOverProjection (SetWeight.diagram P O))).toFunctor.map
      a

private lemma normalizedSectionsConeMap_comp {I : Type u} [SmallCategory I]
    {P Q R : I ⥤ Type u} {E : SSet.{u + 1}} [Quasicategory E]
    (f : P ⟶ Q) (g : Q ⟶ R)
    (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (cP : JoinCone (SetWeight.diagram P O)) (cQ : JoinCone (SetWeight.diagram Q O))
    (cR : JoinCone (SetWeight.diagram R O)) (hcP : IsLimitCone cP)
    (α : (HomotopyCategory.mk (SetWeight.restrictSectionsCone f O cQ) :
      hoFunctor.obj (sliceOver (SetWeight.diagram P O))) ⟶ HomotopyCategory.mk cP)
    (β : (HomotopyCategory.mk (SetWeight.restrictSectionsCone g O cR) :
      hoFunctor.obj (sliceOver (SetWeight.diagram Q O))) ⟶ HomotopyCategory.mk cQ)
    (γ : (HomotopyCategory.mk (SetWeight.restrictSectionsCone (f ≫ g) O cR) :
      hoFunctor.obj (sliceOver (SetWeight.diagram P O))) ⟶ HomotopyCategory.mk cP) :
    normalizedSectionsProjection (f ≫ g) O cP cR γ =
      normalizedSectionsProjection g O cQ cR β ≫ normalizedSectionsProjection f O cP cQ α := by
  let π := (hoFunctor.map (sliceOverProjection (SetWeight.diagram P O))).toFunctor
  let ρ := (hoFunctor.map (sliceOverProjection (SetWeight.diagram Q O))).toFunctor
  let F := (hoFunctor.map (SetWeight.restrictSectionsFunctor f O)).toFunctor
  let a := (SetWeight.restrictSectionsFunctor_vertex f O (SetWeight.restrictSectionsCone g O cR)).trans
    (SetWeight.restrictSectionsCone_comp f O g cR)
  let b := SetWeight.restrictSectionsFunctor_vertex f O cQ
  have hab : eqToHom (congrArg HomotopyCategory.mk a.symm) ≫ F.map β ≫
      eqToHom (congrArg HomotopyCategory.mk b) ≫ α = γ := by
    exact hcP.isTerminalHo.hom_ext _ _
  have hmap :
      π.map (eqToHom (congrArg HomotopyCategory.mk a.symm)) ≫
        π.map (F.map β) ≫ π.map (eqToHom (congrArg HomotopyCategory.mk b)) ≫ π.map α =
      π.map γ := by
    exact (map_four_comp π _ _ _ _).trans (congrArg (fun x => π.map x) hab)
  let tP := congrArg HomotopyCategory.mk (SetWeight.restrictSectionsCone_vertex (f ≫ g) O cR)
  let tQ := congrArg HomotopyCategory.mk (SetWeight.restrictSectionsCone_vertex g O cR)
  let u₁ := congrArg HomotopyCategory.mk (SetWeight.restrictSectionsCone_vertex f O cQ)
  let z₀ := congrArg HomotopyCategory.mk
    (congrArg (fun h => h.app (Opposite.op ⦋0⦌) (SetWeight.restrictSectionsCone g O cR))
      (SetWeight.restrictSectionsFunctor_projection f O))
  let z₁ := congrArg HomotopyCategory.mk
    (congrArg (fun h => h.app (Opposite.op ⦋0⦌) cQ)
      (SetWeight.restrictSectionsFunctor_projection f O))
  have hmid : π.map (eqToHom (congrArg HomotopyCategory.mk b)) =
      eqToHom z₁ ≫ eqToHom u₁.symm := by
    rw [eqToHom_map]
    exact (eqToHom_trans z₁ u₁.symm).symm
  have hstart : eqToHom tP.symm ≫ π.map (eqToHom (congrArg HomotopyCategory.mk a.symm)) ≫
      eqToHom z₀ = eqToHom tQ.symm := by
    rw [eqToHom_map]
    exact eqToHom_three tP.symm _ z₀ tQ.symm
  unfold normalizedSectionsProjection
  have hπ : F ⋙ π = ρ := by
    change (hoFunctor.map (SetWeight.restrictSectionsFunctor f O)).toFunctor ⋙ _ = _
    rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp, SetWeight.restrictSectionsFunctor_projection]
  have hβ' := projection_naturality F π ρ hπ β z₀ z₁
  let ga := congrArg (fun x => π.obj (HomotopyCategory.mk x)) a.symm
  let gb := congrArg (fun x => π.obj (HomotopyCategory.mk x)) b
  simp only [eqToHom_map] at hmap hmid hstart
  have hcalc := @projection_comp_calculation (hoFunctor.obj E) _
    (HomotopyCategory.mk cR.vertex)
    (π.obj (HomotopyCategory.mk (SetWeight.restrictSectionsCone (f ≫ g) O cR)))
    (π.obj (F.obj (HomotopyCategory.mk (SetWeight.restrictSectionsCone g O cR))))
    (π.obj (F.obj (HomotopyCategory.mk cQ)))
    (ρ.obj (HomotopyCategory.mk (SetWeight.restrictSectionsCone g O cR)))
    (ρ.obj (HomotopyCategory.mk cQ))
    (π.obj (HomotopyCategory.mk (SetWeight.restrictSectionsCone f O cQ)))
    (π.obj (HomotopyCategory.mk cP))
    (eqToHom tP.symm)
    (eqToHom ga) (π.map (F.map β))
    (eqToHom gb) (π.map α)
    (eqToHom z₀) (eqToHom z₁) (eqToHom u₁.symm) (eqToHom tQ.symm) (ρ.map β) (π.map γ)
    hmap hmid hβ' hstart
  exact hcalc

private lemma sectionsMap_comp_hom {I : Type u} [SmallCategory I]
    {P Q R : I ⥤ Type u} {E : SSet.{u + 1}} [Quasicategory E]
    (f : P ⟶ Q) (g : Q ⟶ R)
    (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (cP : JoinCone (SetWeight.diagram P O)) (cQ : JoinCone (SetWeight.diagram Q O))
    (cR : JoinCone (SetWeight.diagram R O)) (hcP : IsLimitCone cP) (hcQ : IsLimitCone cQ)
    (hcR : IsLimitCone cR) :
    Truncated.HomotopyCategory.homMk (SetWeight.sectionsMap (f ≫ g) O cP hcP cR hcR).toTruncated =
      Truncated.HomotopyCategory.homMk (SetWeight.sectionsMap g O cQ hcQ cR hcR).toTruncated ≫
      Truncated.HomotopyCategory.homMk (SetWeight.sectionsMap f O cP hcP cQ hcQ).toTruncated := by
  rw [SetWeight.sectionsMap_hom_eq_projection, SetWeight.sectionsMap_hom_eq_projection,
    SetWeight.sectionsMap_hom_eq_projection]
  exact normalizedSectionsConeMap_comp f g O cP cQ cR hcP _ _ _

/-- 同じ三つの指定切断に対して、合成の制限辺の類は逆順の合成となる。 -/
@[cite HTT "1.2.13" (partial := special) "集合重み付き切断の指定極限錐における射の合成。"]
lemma sectionsOf_map_comp_hom :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ {P Q R : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : Q ⟶ R)
 (O : Presheaf C E) (hP : HasLimit (sectionsOfDiagram P O))
 (hQ : HasLimit (sectionsOfDiagram Q O)) (hR : HasLimit (sectionsOfDiagram R O)),
 Truncated.HomotopyCategory.homMk (sectionsOf_map (f ≫ g) O hP hR).toTruncated =
 Truncated.HomotopyCategory.homMk (sectionsOf_map g O hQ hR).toTruncated ≫
 Truncated.HomotopyCategory.homMk (sectionsOf_map f O hP hQ).toTruncated := by
  intro C hC E hE P Q R f g O hP hQ hR
  exact sectionsMap_comp_hom f g O (sectionsOfCone P O hP) (sectionsOfCone Q O hQ)
    (sectionsOfCone R O hR) (sectionsOfCone_isLimit P O hP) (sectionsOfCone_isLimit Q O hQ)
    (sectionsOfCone_isLimit R O hR)

end SerrePositivity.InfinityCategories.Sheaves
