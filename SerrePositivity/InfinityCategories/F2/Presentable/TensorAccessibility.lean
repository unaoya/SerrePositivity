module

public import SerrePositivity.InfinityCategories.F2.Presentable.TensorSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleReflectiveImage

/-!
概要：二項積の反映模型に必要な固定頂点の小ささと filtered 保存を構成する。
方針：元の二射影による写像の検出と、指定余錐の成分判定を使う。
規約：元の単体と全余錐を保持する。
使われ方：presentable 圏の二項積の accessibility。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：二項積の固定頂点写像は両成分の固定頂点写像が小さければ小さい。
方針：元の二射影への合成で小さい二型の積へ単射を作る。
規約：標的の充填性を要求しない。使われ方：積の小さい全部分生成模型。 -/
lemma tensor_hasSmallFixedVertexMaps {X Y : SSet.{u + 1}}
    (hX : Ind.HasSmallFixedVertexMaps X) (hY : Ind.HasSmallFixedVertexMaps Y) :
    Ind.HasSmallFixedVertexMaps (X ⊗ Y) := by
  intro A hA v
  let T := {f : A ⟶ X ⊗ Y // ∀ a, f.app (Opposite.op ⦋0⦌) a = v a}
  let TX := {f : A ⟶ X // ∀ a, f.app (Opposite.op ⦋0⦌) a = (v a).1}
  let TY := {f : A ⟶ Y // ∀ a, f.app (Opposite.op ⦋0⦌) a = (v a).2}
  have : Small.{u} TX := hX A hA (fun a ↦ (v a).1)
  have : Small.{u} TY := hY A hA (fun a ↦ (v a).2)
  let code : T → TX × TY := fun f ↦
    (⟨f.val ≫ fst X Y, fun a ↦ congrArg Prod.fst (f.property a)⟩,
      ⟨f.val ≫ snd X Y, fun a ↦ congrArg Prod.snd (f.property a)⟩)
  apply small_of_injective (f := code)
  intro f g h
  apply Subtype.ext
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg (fun t : TX × TY ↦ t.1.val) h
  · exact congrArg (fun t : TX × TY ↦ t.2.val) h

/-- 概要：同じ κ の filtered 保存関手の二項積は同じ保存性を持つ。
方針：始域の指定余極限を各射影で保存し、標的の成分判定へ渡す。
規約：同じ小さい κ-filtered 全図式を使う。
使われ方：反映の右随伴の二項積の accessibility。 -/
lemma tensorHom_isKappaAccessible {κ : Cardinal.{u}} {C D E F : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E] [Quasicategory F]
    (hC : HasSmallColimits C) (hD : HasSmallColimits D)
    (hE : HasSmallColimits E) (hF : HasSmallColimits F)
    {f : C ⟶ E} {g : D ⟶ F}
    (hf : IsKappaAccessibleFunctor κ f) (hg : IsKappaAccessibleFunctor κ g) :
    IsKappaAccessibleFunctor κ (f ⊗ₘ g) := by
  intro I hI hκ H c hc
  have h := (tensor_isColimitCone_iff_components hC hD c).mp hc
  apply (tensor_isColimitCone_iff_components hE hF (mapJoinCocone (f ⊗ₘ g) c)).mpr
  constructor
  · simpa only [mapJoinCocone, Category.assoc, tensorHom_fst] using
      hf I (H ≫ fst C D) (mapJoinCocone (fst C D) c) h.1
  · simpa only [mapJoinCocone, Category.assoc, tensorHom_snd] using
      hg I (H ≫ snd C D) (mapJoinCocone (snd C D) c) h.2

end SerrePositivity.InfinityCategories.F2.Presentable
