module
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Core.UniverseJoin
public import SerrePositivity.InfinityCategories.Core.UniverseJoinNaturality
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Core.UniverseHorns
public import SerrePositivity.InfinityCategories.Core.UniverseStandardJoins

/-! # 外側ホーンの錐形状の宇宙比較

概要：cospan の錐・span の余錐の持ち上げは大きい宇宙の同じ形状と実同型。
方針：join の自然性と標準単体・ホーンの同型を合成する。
規約：二つの標準三角形を保持する。使われ方：普遍四角形の宇宙比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped Simplicial

/-- cospan の錐の実宇宙同型。 -/
def uliftCospanConeIso :
    (SSet.uliftFunctor.{v, u}).obj (join Δ[0] (horn 2 2 : SSet.{u})) ≅
      join (Δ[0] : SSet.{max u v}) (horn 2 2 : SSet.{max u v}) :=
  uliftJoinIso Δ[0] (horn 2 2) ≪≫
    joinIso (uliftStdSimplexIso 0) (uliftHornIso 2 2)

/-- span の余錐の実宇宙同型。 -/
def uliftSpanCoconeIso :
    (SSet.uliftFunctor.{v, u}).obj (join (horn 2 0 : SSet.{u}) Δ[0]) ≅
      join (horn 2 0 : SSet.{max u v}) (Δ[0] : SSet.{max u v}) :=
  uliftJoinIso (horn 2 0) Δ[0] ≪≫
    joinIso (uliftHornIso 2 0) (uliftStdSimplexIso 0)

/-- 点とホーンの一つの面の join は宇宙比較と可換。 -/
lemma uliftCospanConeIso_face (j : Fin 3) (h : j ≠ 2) :
    (SSet.uliftFunctor.{v, u}).map (joinMap (𝟙 Δ[0]) (horn.ι 2 j h)) ≫
        uliftCospanConeIso.hom =
      (uliftStandardJoinIso.{u, v} 0 1).hom ≫
        joinMap (𝟙 (Δ[0] : SSet.{max u v})) (horn.ι 2 j h) := by
  unfold uliftCospanConeIso uliftStandardJoinIso
  simp only [Iso.trans_hom, joinIso]
  rw [← Category.assoc, uliftJoinIso_hom_naturality]
  simp only [Category.assoc, ← joinMap_comp]
  rw [uliftHornIso_face]
  simp only [(SSet.uliftFunctor.{v, u}).map_id, Category.id_comp, Category.comp_id]

/-- ホーンの一つの面と点の join も宇宙比較と可換。 -/
lemma uliftSpanCoconeIso_face (j : Fin 3) (h : j ≠ 0) :
    (SSet.uliftFunctor.{v, u}).map (joinMap (horn.ι 0 j h) (𝟙 Δ[0])) ≫
        uliftSpanCoconeIso.hom =
      (uliftStandardJoinIso.{u, v} 1 0).hom ≫
        joinMap (horn.ι 0 j h) (𝟙 (Δ[0] : SSet.{max u v})) := by
  unfold uliftSpanCoconeIso uliftStandardJoinIso
  simp only [Iso.trans_hom, joinIso]
  rw [← Category.assoc, uliftJoinIso_hom_naturality]
  simp only [Category.assoc, ← joinMap_comp]
  rw [uliftHornIso_face]
  simp only [(SSet.uliftFunctor.{v, u}).map_id, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories
