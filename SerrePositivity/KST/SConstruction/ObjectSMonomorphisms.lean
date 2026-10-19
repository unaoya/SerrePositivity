module
public import SerrePositivity.KST.SConstruction.ObjectSVertices

/-! # object S 構成による単射の保存
概要：底の完全関手が単射なら、全 object S の単体の写像も単射。
方針：実際の Ar 図式へ戻し、底の単射で後合成を消去する。
規約：頂点の単射だけには弱めない。使われ方：相対図式の射とホモトピーの等号の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 底で単射な完全関手の object S への作用は各次数で単射。 -/
lemma objectSConstructionFunctor_map_injective {X Y : StableModel.{u}} (f : X ⟶ Y) [Mono f.val]
    (n : SimplexCategoryᵒᵖ) : Function.Injective ((objectSConstructionFunctor.map f).app n) := by
  intro v w h
  apply gappedDiagram_injective
  apply (cancel_mono f.val).1
  have he := congrArg gappedDiagram h
  rw [gappedDiagram_objectSFunctor_map, gappedDiagram_objectSFunctor_map] at he
  exact he

/-- 底で単射な完全関手は object S 構成の単射を誘導する。 -/
instance objectSConstructionFunctor_map_mono {X Y : StableModel.{u}} (f : X ⟶ Y) [Mono f.val] :
    Mono (objectSConstructionFunctor.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  exact objectSConstructionFunctor_map_injective f n

end SerrePositivity.KST.SConstruction
