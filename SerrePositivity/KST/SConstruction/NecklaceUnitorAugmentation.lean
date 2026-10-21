module
public import SerrePositivity.KST.SConstruction.NecklaceWedgeInclusions
public import SerrePositivity.KST.SConstruction.NecklaceInPoint
public import SerrePositivity.KST.SConstruction.NecklaceInWedge

/-! # 左右単位と元の K への augmentation
概要：固定端点の一点 necklace を貼った augmentation が、元の左右単位と可換となる。
方針：元の点との包含が構造同型の逆であることを示し、その包含で射を判定する。
規約：全単体的写像を保持。使われ方：K 内の左右単位と cubical 合成の単位則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 左の一点を貼る元の右包含は、全単体を保つ同型。 -/
instance necklacePointInr_isIso (T : Necklace.{u}) :
    IsIso (necklacePoint.down.wedgeInr.{u} T.down) := by
  let e : (necklacePoint.down.wedge T.down).carrier.{u} ≅ T.down.carrier.{u} :=
    necklaceSimplicialSet.mapIso (necklaceLeftUnitor T)
  have h : necklacePoint.down.wedgeInr T.down = e.inv := by
    apply (cancel_mono e.hom).mp
    exact (necklaceLeftUnitor_inr T).trans e.inv_hom_id.symm
  rw [h]
  infer_instance

/-- 右の一点を貼る元の左包含は、全単体を保つ同型。 -/
instance necklacePointInl_isIso (T : Necklace.{u}) :
    IsIso (T.down.wedgeInl.{u} necklacePoint.down) := by
  let e : (T.down.wedge necklacePoint.down).carrier.{u} ≅ T.down.carrier.{u} :=
    necklaceSimplicialSet.mapIso (necklaceRightUnitor T)
  have h : T.down.wedgeInl necklacePoint.down = e.inv := by
    apply (cancel_mono e.hom).mp
    exact (necklaceRightUnitor_inl T).trans e.inv_hom_id.symm
  rw [h]
  infer_instance

/-- 元の右包含で回収できる augmentation は、元の左単位による合成そのもの。 -/
lemma necklaceLeftUnitor_desc (T : Necklace.{u}) {K : SSet.{u}} (f : T.down.carrier ⟶ K)
    (l : (necklacePoint.down.wedge T.down).carrier ⟶ K)
    (h : necklacePoint.down.wedgeInr T.down ≫ l = f) :
    (necklaceLeftUnitor T).hom.map ≫ f = l := by
  apply (cancel_epi (necklacePoint.down.wedgeInr T.down)).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ f) (necklaceLeftUnitor_inr T)).trans
      ((Category.id_comp f).trans h.symm))

/-- 元の左包含で回収できる augmentation は、元の右単位による合成そのもの。 -/
lemma necklaceRightUnitor_desc (T : Necklace.{u}) {K : SSet.{u}} (f : T.down.carrier ⟶ K)
    (l : (T.down.wedge necklacePoint.down).carrier ⟶ K)
    (h : T.down.wedgeInl necklacePoint.down ≫ l = f) :
    (necklaceRightUnitor T).hom.map ≫ f = l := by
  apply (cancel_epi (T.down.wedgeInl necklacePoint.down)).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ f) (necklaceRightUnitor_inl T)).trans
      ((Category.id_comp f).trans h.symm))

/-- 左の元の一点 necklace と貼った augmentation は、元の左単位と厳密に可換。 -/
lemma necklaceInLeftUnitor_augmentation {K : SSet.{u}} {x y : K _⦋0⦌}
    (T : NecklaceIn K x y) :
    (necklaceLeftUnitor T.necklace).hom.map ≫ T.map =
      (necklaceInWedge (necklaceInPoint K x) T).map :=
  necklaceLeftUnitor_desc T.necklace T.map _ (necklaceInWedge_inr (necklaceInPoint K x) T)

/-- 右の元の一点 necklace と貼った augmentation は、元の右単位と厳密に可換。 -/
lemma necklaceInRightUnitor_augmentation {K : SSet.{u}} {x y : K _⦋0⦌}
    (T : NecklaceIn K x y) :
    (necklaceRightUnitor T.necklace).hom.map ≫ T.map =
      (necklaceInWedge T (necklaceInPoint K y)).map :=
  necklaceRightUnitor_desc T.necklace T.map _ (necklaceInWedge_inl T (necklaceInPoint K y))

end SerrePositivity.KST.SConstruction
