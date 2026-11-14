module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeInclusions
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceInPoint
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceInWedge

/-! # 左右単位と元の K への augmentation
概要：固定端点の一点 necklace を貼った augmentation が、元の左右単位と可換となる。
方針：元の点との包含が構造同型の逆であることを示し、その包含で射を判定する。
規約：全単体的写像を保持。使われ方：K 内の左右単位と cubical 合成の単位則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 左の一点を貼る元の右包含は、全単体を保つ同型。 -/
instance necklacePointInr_isIso (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeInr.{u} T.down) := by
  let e : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedge T.down).carrier.{u} ≅ T.down.carrier.{u} :=
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet.mapIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T)
  have h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeInr T.down = e.inv := by
    apply (cancel_mono e.hom).mp
    exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_inr T).trans e.inv_hom_id.symm
  rw [h]
  infer_instance

/-- 右の一点を貼る元の左包含は、全単体を保つ同型。 -/
instance necklacePointInl_isIso (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    IsIso (T.down.wedgeInl.{u} _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down) := by
  let e : (T.down.wedge _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down).carrier.{u} ≅ T.down.carrier.{u} :=
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet.mapIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T)
  have h : T.down.wedgeInl _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down = e.inv := by
    apply (cancel_mono e.hom).mp
    exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_inl T).trans e.inv_hom_id.symm
  rw [h]
  infer_instance

/-- 元の右包含で回収できる augmentation は、元の左単位による合成そのもの。 -/
lemma necklaceLeftUnitor_desc (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) {K : SSet.{u}} (f : T.down.carrier ⟶ K)
    (l : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedge T.down).carrier ⟶ K)
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeInr T.down ≫ l = f) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T).hom.map ≫ f = l := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeInr T.down)).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_inr T)).trans
      ((Category.id_comp f).trans h.symm))

/-- 元の左包含で回収できる augmentation は、元の右単位による合成そのもの。 -/
lemma necklaceRightUnitor_desc (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) {K : SSet.{u}} (f : T.down.carrier ⟶ K)
    (l : (T.down.wedge _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down).carrier ⟶ K)
    (h : T.down.wedgeInl _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down ≫ l = f) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T).hom.map ≫ f = l := by
  apply (cancel_epi (T.down.wedgeInl _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down)).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_inl T)).trans
      ((Category.id_comp f).trans h.symm))

/-- 左の元の一点 necklace と貼った augmentation は、元の左単位と厳密に可換。 -/
lemma necklaceInLeftUnitor_augmentation {K : SSet.{u}} {x y : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T.necklace).hom.map ≫ T.map =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x) T).map :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_desc T.necklace T.map _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x) T)

/-- 右の元の一点 necklace と貼った augmentation は、元の右単位と厳密に可換。 -/
lemma necklaceInRightUnitor_augmentation {K : SSet.{u}} {x y : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T.necklace).hom.map ≫ T.map =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K y)).map :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_desc T.necklace T.map _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K y))

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInLeftUnitor_augmentation := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInLeftUnitor_augmentation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInRightUnitor_augmentation := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInRightUnitor_augmentation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceLeftUnitor_desc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_desc

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePointInl_isIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklacePointInl_isIso := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePointInl_isIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePointInr_isIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklacePointInr_isIso := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePointInr_isIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceRightUnitor_desc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_desc
