module

public import SerrePositivity.InfinityCategories.F2.Ind.NativeKanColimitTransfer
public import SerrePositivity.InfinityCategories.F2.Ind.NativeCoconePreservationTransport

/-!
概要：元の余極限と同じ像の余極限を、両側の native 余錐制限で同時に輸送する。
方針：制限の本質全射性で全余錐を持ち上げ、両側の始対象性を反映する。
規約：像の頂点だけでなく、元の全余錐の保存を要求する。
使われ方：I-2 d′ の有限形状帰納における保存性の述語。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ元の全余錐と、その元の関手による像がともに余極限であること。 -/
def HasPreservedColimit {K X Y : SSet.{u}} (G : X ⟶ Y) (p : K ⟶ X) : Prop :=
  ∃ c : JoinCocone p, IsColimitCone c ∧ IsColimitCone (mapJoinCocone G c)

/-- 両側の native 制限同値は、元の全余錐の保存を伴う存在を保ち反映する。 -/
lemma hasPreservedColimit_iff_nativeRestriction
    {A K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : K ⟶ X) (i : A ⟶ K) (G : X ⟶ Y)
    (hi : IsQCatEquivalence (sliceUnderRestrict p i))
    (hiG : IsQCatEquivalence (sliceUnderRestrict (p ≫ G) i)) :
    HasPreservedColimit G p ↔ HasPreservedColimit G (i ≫ p) := by
  constructor
  · rintro ⟨c, hc, hGc⟩
    refine ⟨c.restrict i, (hi.choose.isInitialVertex_iff c).mp hc, ?_⟩
    have h := (hiG.choose.isInitialVertex_iff (mapJoinCocone G c)).mp hGc
    change IsColimitCone ((mapJoinCocone G c).restrict i) at h
    exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _).symm).mp h
  · rintro ⟨d, hd, hGd⟩
    obtain ⟨a₀, ⟨e⟩⟩ := hi.choose.isEssentiallySurjective d
    let a : JoinCocone p := a₀
    have he : VertexIso (X := sliceUnder (i ≫ p)) (a.restrict i) d := e
    have ha : IsColimitCone a := (hi.choose.isInitialVertex_iff a).mpr
      (hd.of_vertexIso he.symm)
    refine ⟨a, ha, ?_⟩
    have ht := hGd.of_vertexIso (VertexIso.map he (sliceUnderPostcomp (i ≫ p) G)).symm
    change IsColimitCone (mapJoinCocone G (a.restrict i)) at ht
    apply (hiG.choose.isInitialVertex_iff (mapJoinCocone G a)).mpr
    change IsColimitCone ((mapJoinCocone G a).restrict i)
    exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _)).mp ht

/-- 一つの保存された余極限があれば、元の任意の余極限全余錐も同じ関手で保存。 -/
lemma HasPreservedColimit.map_isColimit {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {G : X ⟶ Y} {p : K ⟶ X}
    (h : HasPreservedColimit G p) (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone G c) := by
  obtain ⟨d, hd, hGd⟩ := h
  exact hGd.of_vertexIso (VertexIso.map (colimitConeIso d c hd hc) (sliceUnderPostcomp p G))

end SerrePositivity.InfinityCategories.F2.Ind
