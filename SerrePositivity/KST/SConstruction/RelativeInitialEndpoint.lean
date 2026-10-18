module
public import SerrePositivity.KST.SConstruction.RelativeInitialCosliceComparison
public import SerrePositivity.InfinityCategories.Core.CosliceEndpointFibration

/-! # 相対始対象の coslice の端点比較
概要：相対始対象の coslice は、像の coslice と元の対象を合わせた引き戻しへ trivial Kan fibration で写る。
方針：空図式の coslice と端点の一致を使い、相対 coslice の全境界持ち上げへ移す。
規約：quasicategory 性やファイブレーション性は要求しない。
使われ方：HTT §1.2.12・§2.1.2、固定した図式上での余極限の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：空図式の coslice への二つの射は端点への射が等しければ等しい。
方針：空の左因子との join の同型で uncurry の射を比較する。
規約：K は空部分複体を取るための任意の単体集合。
使われ方：端点を使う相対 coslice の比較。 -/
lemma sliceUnder_empty_hom_ext {K A X : SSet.{u}} (p : ((⊥ : K.Subcomplex) : SSet.{u}) ⟶ X)
    (f g : A ⟶ sliceUnder p) (h : f ≫ sliceUnderProjection p = g ≫ sliceUnderProjection p) :
    f = g := by
  apply sliceUnderUncurry_injective p
  apply (cancel_epi (emptyJoinIso K A).inv).1
  rw [emptyJoinIso_inv, sliceUnderUncurry_projection, sliceUnderUncurry_projection]
  exact h

/-- 概要：相対始対象の coslice の端点比較は trivial Kan fibration。
方針：空の図式上の coslice の部分を端点から作り、相対 coslice 比較の全境界持ち上げを使う。
規約：p は任意の射、a は相対始点境界充填を持つ点。
使われ方：相対始対象から任意のパラメーターへの射を基底上で選ぶ。 -/
lemma cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting {X Y : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ X) (p : X ⟶ Y)
    (ha : InitialBoundaryLifting p (SSet.yonedaEquiv a)) :
    TrivialKanFibration (cosliceEndpointMap a p) := by
  have ht : TrivialKanFibration (relativeCosliceMap a p (⊥ : (Δ[0] : SSet.{u}).Subcomplex)) := by
    exact (congrArg (fun Z : (Δ[0] : SSet.{u}).Subcomplex =>
      TrivialKanFibration (relativeCosliceMap a p Z)) boundary_zero).mp
        (relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting a p ha)
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro u b sq
  let K₀ : (Δ[0] : SSet.{u}).Subcomplex := ⊥
  let r := pullback.fst p (sliceUnderProjection (a ≫ p))
  let s := pullback.snd p (sliceUnderProjection (a ≫ p))
  let H := (emptyJoinIso (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u})).hom ≫ b ≫ r
  have hH : joinInl (K₀ : SSet.{u}) Δ[n] ≫ H = K₀.ι ≫ a :=
    Subcomplex.isInitialBot.hom_ext _ _
  let e := sliceUnderCurry H hH
  have he : e ≫ sliceUnderProjection (K₀.ι ≫ a) = b ≫ r := by
    rw [sliceUnderCurry_projection]
    dsimp only [H]
    rw [← emptyJoinIso_inv, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hw : e ≫ sliceUnderPostcomp (K₀.ι ≫ a) p =
      (b ≫ s) ≫ sliceUnderRestrict (a ≫ p) K₀.ι := by
    apply sliceUnder_empty_hom_ext
    change (e ≫ sliceUnderProjection (K₀.ι ≫ a)) ≫ p =
      b ≫ s ≫ sliceUnderProjection (a ≫ p)
    rw [he, Category.assoc]
    simpa only [Category.assoc] using
      congrArg (fun f => b ≫ f) (pullback.condition (f := p) (g := sliceUnderProjection (a ≫ p)))
  let d : (Δ[n] : SSet.{u}) ⟶ relativeCosliceTarget a p K₀ := pullback.lift e (b ≫ s) hw
  have hd₁ : d ≫ pullback.fst (sliceUnderPostcomp (K₀.ι ≫ a) p)
      (sliceUnderRestrict (a ≫ p) K₀.ι) = e := pullback.lift_fst _ _ _
  have hd₂ : d ≫ pullback.snd (sliceUnderPostcomp (K₀.ι ≫ a) p)
      (sliceUnderRestrict (a ≫ p) K₀.ι) = b ≫ s := pullback.lift_snd _ _ _
  have hs : CommSq u (boundary n).ι (relativeCosliceMap a p K₀) d := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeCosliceMap, pullback.lift_fst, hd₁]
      apply sliceUnder_empty_hom_ext
      change u ≫ sliceUnderProjection a = (boundary n).ι ≫ e ≫
        sliceUnderProjection (K₀.ι ≫ a)
      rw [he]
      have hh := congrArg (fun f => f ≫ r) sq.w
      simpa only [r, Category.assoc, cosliceEndpointMap_fst] using hh
    · simp only [Category.assoc, relativeCosliceMap, pullback.lift_snd, hd₂]
      have hh := congrArg (fun f => f ≫ s) sq.w
      simpa only [s, Category.assoc, cosliceEndpointMap_snd] using hh
  have : HasLiftingProperty (boundary n).ι (relativeCosliceMap a p K₀) :=
    ht.mem _ inferInstance
  refine CommSq.HasLift.mk' {
    l := hs.lift
    fac_left := hs.fac_left
    fac_right := ?_ }
  apply pullback.hom_ext
  · rw [Category.assoc, cosliceEndpointMap_fst]
    have hh := congrArg (fun f => f ≫
      pullback.fst (sliceUnderPostcomp (K₀.ι ≫ a) p) (sliceUnderRestrict (a ≫ p) K₀.ι)) hs.fac_right
    simp only [Category.assoc, relativeCosliceMap, pullback.lift_fst, hd₁] at hh
    have hh' := congrArg (fun f => f ≫ sliceUnderProjection (K₀.ι ≫ a)) hh
    change hs.lift ≫ sliceUnderProjection a = e ≫ sliceUnderProjection (K₀.ι ≫ a) at hh'
    exact hh'.trans he
  · rw [Category.assoc, cosliceEndpointMap_snd]
    have hh := congrArg (fun f => f ≫
      pullback.snd (sliceUnderPostcomp (K₀.ι ≫ a) p) (sliceUnderRestrict (a ≫ p) K₀.ι)) hs.fac_right
    simpa only [Category.assoc, relativeCosliceMap, pullback.lift_snd, hd₂] using hh

/-- 概要：相対始対象の coslice への射は、端点と基底の余錐を保って任意の単射に沿い延長できる。
方針：二つの指定を引き戻しへ合わせ、端点比較の trivial Kan fibration で持ち上げる。
規約：A・B・X・Y の quasicategory 性は要求しない。
使われ方：cofiber の零頂点・零射を固定するための相対輸送。 -/
lemma exists_relativeInitialCosliceLift {A B X Y : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ X) (p : X ⟶ Y)
    (ha : InitialBoundaryLifting p (SSet.yonedaEquiv a)) (i : A ⟶ B) [Mono i]
    (u : A ⟶ sliceUnder a) (v : B ⟶ X) (w : B ⟶ sliceUnder (a ≫ p))
    (hv : v ≫ p = w ≫ sliceUnderProjection (a ≫ p))
    (hu₁ : u ≫ sliceUnderProjection a = i ≫ v)
    (hu₂ : u ≫ sliceUnderPostcomp a p = i ≫ w) :
    ∃ F : B ⟶ sliceUnder a, i ≫ F = u ∧
      F ≫ sliceUnderProjection a = v ∧ F ≫ sliceUnderPostcomp a p = w := by
  have ht := cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting a p ha
  have := ht.mem i inferInstance
  let d : B ⟶ pullback p (sliceUnderProjection (a ≫ p)) := pullback.lift v w hv
  have hs : CommSq u i (cosliceEndpointMap a p) d := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, cosliceEndpointMap_fst, d, pullback.lift_fst]
      exact hu₁
    · simp only [Category.assoc, cosliceEndpointMap_snd, d, pullback.lift_snd]
      exact hu₂
  refine ⟨hs.lift, hs.fac_left, ?_, ?_⟩
  · have he := congrArg (fun f => f ≫ pullback.fst p (sliceUnderProjection (a ≫ p))) hs.fac_right
    simpa only [Category.assoc, cosliceEndpointMap_fst, d, pullback.lift_fst] using he
  · have he := congrArg (fun f => f ≫ pullback.snd p (sliceUnderProjection (a ≫ p))) hs.fac_right
    simpa only [Category.assoc, cosliceEndpointMap_snd, d, pullback.lift_snd] using he

end SerrePositivity.KST.SConstruction
