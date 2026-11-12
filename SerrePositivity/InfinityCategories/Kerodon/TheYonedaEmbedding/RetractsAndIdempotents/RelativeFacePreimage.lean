module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：元の部分複体の包含を、元の大きい面の標準同型へ引き戻す。
方針：元の面への包含と同型の合成の逆像から、元の小さい面への同型を構成する。
規約：同型の後の包含の正方形は厳密に可換。
使われ方：指定した面のホーンを標準ホーンの元の包含へ照合する。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の大きい部分複体の座標での逆像は、元の小さい部分複体と同型。 -/
lemma relativeFacePreimage_isIso {X Z : SSet.{u}} {A B : X.Subcomplex}
    (h : A ≤ B) (e : Z ≅ (B : SSet.{u})) :
    IsIso (A.fromPreimage (e.hom ≫ B.ι)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply Subtype.ext
    apply (CategoryTheory.mono_iff_injective ((e.hom ≫ B.ι).app n)).mp inferInstance
    exact congrArg (fun t : A.obj n ↦ t.val) hab
  · intro a
    let b : B.obj n := ⟨a.val, h n a.property⟩
    obtain ⟨z, hz⟩ := ((CategoryTheory.isIso_iff_bijective (e.hom.app n)).mp
      inferInstance).surjective b
    refine ⟨⟨z, ?_⟩, ?_⟩
    · change (e.hom.app n z).val ∈ A.obj n
      rw [hz]
      exact a.property
    · apply Subtype.ext
      change (e.hom.app n z).val = a.val
      exact congrArg (fun t : B.obj n ↦ t.val) hz

/-- 元の包含と、同じ座標へ引き戻した包含の厳密な矢印同型。 -/
def relativeFacePreimageArrowIso {X Z : SSet.{u}} {A B : X.Subcomplex}
    (h : A ≤ B) (e : Z ≅ (B : SSet.{u})) :
    Arrow.mk (A.preimage (e.hom ≫ B.ι)).ι ≅ Arrow.mk (Subcomplex.homOfLE h) := by
  haveI := relativeFacePreimage_isIso h e
  refine Arrow.isoMk (asIso (A.fromPreimage (e.hom ≫ B.ι))) e ?_
  change A.fromPreimage (e.hom ≫ B.ι) ≫ Subcomplex.homOfLE h =
    (A.preimage (e.hom ≫ B.ι)).ι ≫ e.hom
  apply (cancel_mono B.ι).mp
  rw [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.fromPreimage_ι, Category.assoc]


end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
