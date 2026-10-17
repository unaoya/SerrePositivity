module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.DifferentialGraded.Perfect.KaroubiEquivalence
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty

/-! # Perf 判定の生成条件と本質像の厚さ

厚い生成性を他の二条件とは独立に定義する。生成対象の任意余積は要求しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w u₁ u₂ v₁ v₂
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Pretriangulated

/-- 冪等完備な圏からの充満忠実関手の本質像は retract に閉じる。 -/
lemma criterionPerfEssImage_retract_closed
    {C : Type u₁} [Category.{v₁} C] [IsIdempotentComplete C]
    {T : Type u₂} [Category.{v₂} T] (F : C ⥤ T) [F.Full] [F.Faithful] :
    F.essImage.IsStableUnderRetracts where
  of_retract {Z Y} t hY := by
    obtain ⟨X, ⟨e⟩⟩ := hY
    let a : Retract Z (F.obj X) := t.trans (Retract.ofIso e.symm)
    let p : X ⟶ X := F.preimage (a.r ≫ a.i)
    have hp : F.map p = a.r ≫ a.i := F.map_preimage _
    have hpp : p ≫ p = p := by
      apply F.map_injective
      rw [F.map_comp, hp]
      simp only [Category.assoc, a.retract_assoc]
    obtain ⟨X', i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split X p hpp
    have hi : i ≫ p = i := by rw [← hri, ← Category.assoc, hir, Category.id_comp]
    refine ⟨X', ⟨{
      hom := F.map i ≫ a.r
      inv := a.i ≫ F.map r
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩⟩
    · calc
        (F.map i ≫ a.r) ≫ (a.i ≫ F.map r) = F.map (i ≫ p ≫ r) := by
          simp only [F.map_comp, hp, Category.assoc]
        _ = 𝟙 _ := by rw [← Category.assoc, hi, hir, F.map_id]
    · calc
        (a.i ≫ F.map r) ≫ (F.map i ≫ a.r) = a.i ≫ F.map p ≫ a.r := by
          rw [← hri, F.map_comp]
          simp only [Category.assoc]
        _ = 𝟙 _ := by simp only [hp, Category.assoc, a.retract_assoc, a.retract]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

local instance : (perfectModuleInclusion A E Set.univ).Full :=
  inferInstanceAs ((modulePerfect A E).ι.Full)
local instance : (perfectModuleInclusion A E Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect A E).ι.Faithful)

/-- 各列を含む厚い部分圏は Perf(E) を含む。列の perfect 性は別条件。 -/
def criterionPerfColumnsThickGenerate : Prop :=
  ∀ (P : ObjectProperty (DerivedModuleCategory A E)),
    P.IsTriangulated → P.IsClosedUnderIsomorphisms → P.IsStableUnderRetracts →
    (∀ d : D, P ((kernelDerivedColumn A D E d).obj K)) → modulePerfect A E ≤ P

/-- 作用の像を含む厚い性質は、列を含むかどうかだけで決まる。 -/
lemma criterionPerf_image_le_iff_columns
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts] :
    (∀ X, modulePerfect A D X → P ((kernelDerivedTensor A D E K).obj X)) ↔
      ∀ d : D, P ((kernelDerivedColumn A D E d).obj K) := by
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  let : (P.inverseImage (kernelDerivedTensor A D E K)).IsStableUnderRetracts :=
    ⟨fun t ht => P.prop_of_retract (t.map (kernelDerivedTensor A D E K)) ht⟩
  constructor
  · intro h d
    exact P.prop_of_iso (kernelDerivedColumnActionIso A D E K d)
      (h _ (modulePerfectOver_representable A D d (Set.mem_univ d)))
  · intro h
    exact (modulePerfect_le_iff_generators A D (P.inverseImage
      (kernelDerivedTensor A D E K))).2 (fun d =>
        P.prop_of_iso (kernelDerivedColumnActionIso A D E K d).symm (h d))

/-- 充満忠実性を確保した後は、厚い生成性だけで Perf 上の本質的全射が従う。 -/
lemma criterionPerf_essSurj_of_columnsThickGenerate
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).Full]
    [(perfectDerivedKernelAction A D E K hK).Faithful]
    (hgen : criterionPerfColumnsThickGenerate A D E K) :
    (perfectDerivedKernelAction A D E K hK).EssSurj := by
  let F := perfectDerivedKernelAction A D E K hK
  let := criterionPerfActionCommShift A D E K hK
  let := criterionPerfActionIsTriangulated A D E K hK
  let G := F ⋙ perfectModuleInclusion A E Set.univ
  let : G.essImage.IsStableUnderRetracts := criterionPerfEssImage_retract_closed G
  have hcols : ∀ d : D, G.essImage ((kernelDerivedColumn A D E d).obj K) := by
    intro d
    exact ⟨⟨_, modulePerfectOver_representable A D d (Set.mem_univ d)⟩,
      ⟨kernelDerivedColumnActionIso A D E K d⟩⟩
  have hle := hgen G.essImage inferInstance inferInstance inferInstance hcols
  refine ⟨fun Y => ?_⟩
  obtain ⟨X, ⟨e⟩⟩ := hle Y.obj Y.property
  exact ⟨X, ⟨(perfectModuleInclusion A E Set.univ).preimageIso e⟩⟩

/-- 本質的全射な実際の Perf 作用の列は Perf(E) を厚く生成する。 -/
lemma criterionPerf_columnsThickGenerate_of_essSurj
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).EssSurj] :
    criterionPerfColumnsThickGenerate A D E K := by
  intro P htri hiso hret hcols Y hY
  let F := perfectDerivedKernelAction A D E K hK
  have himage := (criterionPerf_image_le_iff_columns A D E K P).2 hcols
  let Y' : PerfectModuleCategory A E := ⟨Y, hY⟩
  let X := F.objPreimage Y'
  exact P.prop_of_iso
    ((perfectModuleInclusion A E Set.univ).mapIso (F.objObjPreimageIso Y'))
    (himage X.obj X.property)

/-- Perf 上では任意余積による生成性は不要で、厚い生成性で足りる。 -/
lemma criterionPerf_essSurj_iff_columnsThickGenerate
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).Full]
    [(perfectDerivedKernelAction A D E K hK).Faithful] :
    (perfectDerivedKernelAction A D E K hK).EssSurj ↔
      criterionPerfColumnsThickGenerate A D E K := by
  constructor
  · intro h
    exact criterionPerf_columnsThickGenerate_of_essSurj A D E K hK
  · exact criterionPerf_essSurj_of_columnsThickGenerate A D E K hK

end SerrePositivity.DifferentialGraded.Morita
