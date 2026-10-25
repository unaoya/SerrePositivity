module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFamilySaturation
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleIndRepresentation

/-!
概要：一般の accessible 圏内の小さい対象族の同型飽和に小さい全同値模型を与える。
方針：Ind 模型で縮小し、元の全同値を同型飽和へ制限して戻す。
規約：元の圏に固定頂点写像の厳密な小ささを要求しない。
使われ方：compact 候補と元の固定対象を含む小さい comma 模型の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：対象族の同型飽和は元の頂点同型で不変。
方針：指定された同型を代表族への同型に合成する。
規約：代表族は変更しない。
使われ方：全同値の全部分圏への制限。 -/
lemma familySaturation_iff_vertexIso {C : SSet.{u + 1}} [Quasicategory C]
    {T : Type u} (v : T → C _⦋0⦌) {x y : C _⦋0⦌} (e : VertexIso x y) :
    FamilySaturation v x ↔ FamilySaturation v y := by
  constructor
  · rintro ⟨t, ⟨h⟩⟩
    exact ⟨t, ⟨e.symm ≪≫ h⟩⟩
  · rintro ⟨t, ⟨h⟩⟩
    exact ⟨t, ⟨e ≪≫ h⟩⟩

/-- 概要：逆全同値で戻した族の同型飽和は元の族の同型飽和を反映する。
方針：同型を全同値で写し、単位・余単位の成分を合成する。
規約：元の全対象族を保持する。
使われ方：Ind 模型上の同型飽和の比較。 -/
lemma familySaturation_iff_equivalence {M C : SSet.{u + 1}}
    [Quasicategory M] [Quasicategory C] (e : QCatEquivalence M C)
    {T : Type u} (v : T → C _⦋0⦌) (x : M _⦋0⦌) :
    FamilySaturation (fun t ↦ e.inv.app (Opposite.op ⦋0⦌) (v t)) x ↔
      FamilySaturation v (e.hom.app (Opposite.op ⦋0⦌) x) := by
  constructor
  · rintro ⟨t, ⟨h⟩⟩
    exact ⟨t, ⟨VertexIso.map h e.hom ≪≫ e.invHomIso.app (v t)⟩⟩
  · rintro ⟨t, ⟨h⟩⟩
    exact ⟨t, ⟨(e.homInvIso.app x).symm ≪≫ VertexIso.map h e.inv⟩⟩

/-- 概要：元の全同値は逆で戻した族と元の族の同型飽和の全同値を誘導する。
方針：同型飽和の反映と元の全同値の全部分制限を使う。
規約：順方向の関手は元の全同値の制限。
使われ方：具体的な小さい模型から元の圏への帰還。 -/
def familySaturationEquivalence {M C : SSet.{u + 1}}
    [Quasicategory M] [Quasicategory C] (e : QCatEquivalence M C)
    {T : Type u} (v : T → C _⦋0⦌) :
    QCatEquivalence
      (familySaturationCategory (fun t ↦ e.inv.app (Opposite.op ⦋0⦌) (v t)))
      (familySaturationCategory v) := by
  let w := fun t ↦ e.inv.app (Opposite.op ⦋0⦌) (v t)
  let r := fullSubcomplexLift (FamilySaturation v)
    (familySaturationInclusion w ≫ e.hom) (fun z ↦
      (familySaturation_iff_equivalence e v z.val).mp (fullSubcomplexOnVertices_vertex z))
  exact (isQCatEquivalence_fullSubcomplexRestriction (FamilySaturation w) (FamilySaturation v)
    (fun h ↦ familySaturation_iff_vertexIso v h) e.hom e.isQCatEquivalence r rfl
    (fun x hx ↦ (familySaturation_iff_equivalence e v x).mpr hx)).choose

/-- 概要：accessible 圏内の小さい対象族の同型飽和は小さい ∞ 圏と全同値。
方針：具体的な Ind 模型で族を縮小し、同型飽和の制限同値で戻す。
規約：元の圏への厳密な固定頂点小ささの仮定は不要。
使われ方：compact 候補と固定対象を含む小さい模型。 -/
lemma IsAccessible.exists_smallFamilySaturationModel {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsAccessible C) {T : Type u} (v : T → C _⦋0⦌) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (familySaturationCategory v)) := by
  obtain ⟨κ, hκ⟩ := hC
  obtain ⟨K, hK, ⟨e⟩⟩ := hκ.exists_indEquivalence
  have := hK
  let w := fun t ↦ e.inv.app (Opposite.op ⦋0⦌) (v t)
  let hs := Ind.ind_hasSmallFixedVertexMaps κ K
  exact ⟨smallFullModel hs w, inferInstance,
    ⟨(smallFamilySaturationEquivalence w hs).trans (familySaturationEquivalence e v)⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
