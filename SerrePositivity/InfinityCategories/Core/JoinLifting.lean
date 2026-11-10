module

public import SerrePositivity.InfinityCategories.Core.JoinCells
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：pushout-join の貼り合わせと持ち上げ問題の移送。
方針：部分複体の交わりと和を圏論的な pushout に直し、slice の普遍性を適用する。
規約：join の左右と left/right anodyne の向きは JoinCells と一致させる。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の生成セルからの閉包。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial

namespace SerrePositivity.InfinityCategories

/-- 概要：左右両方の部分複体の join の像は、左右の join の交わり。
方針：切断位置を保ったまま両因子をそれぞれ持ち上げる。
規約：空区間の持ち上げも augMem_iff_exists が処理する。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の貼り合わせ。 -/
lemma joinMap_range_inf {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    Subfunctor.range (joinMap A₀.ι B₀.ι) =
      joinSubcomplexLeft A₀ B ⊓ joinSubcomplexRight A B₀ := by
  ext ⟨⟨n⟩⟩ s
  change (∃ t, (joinMap A₀.ι B₀.ι).app (Opposite.op ⦋n⦌) t = s) ↔
    s ∈ (joinSubcomplexLeft A₀ B).obj (Opposite.op ⦋n⦌) ∧
    s ∈ (joinSubcomplexRight A B₀).obj (Opposite.op ⦋n⦌)
  rw [Join.mem_joinSubcomplexLeft, Join.mem_joinSubcomplexRight]
  rcases s with ⟨ℓ, a, b⟩
  constructor
  · rintro ⟨⟨c, x, y⟩, h⟩
    have hc : c = ℓ := congrArg Sigma.fst h
    subst c
    have hab := eq_of_heq (Sigma.mk.inj h).2
    exact ⟨(Join.augMem_iff_exists A₀ _ _).2 ⟨x, congrArg Prod.fst hab⟩,
      (Join.augMem_iff_exists B₀ _ _).2 ⟨y, congrArg Prod.snd hab⟩⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨x, hx⟩ := (Join.augMem_iff_exists A₀ _ _).1 ha
    obtain ⟨y, hy⟩ := (Join.augMem_iff_exists B₀ _ _).1 hb
    refine ⟨⟨ℓ, x, y⟩, ?_⟩
    change (⟨ℓ, Join.augHom A₀.ι _ x, Join.augHom B₀.ι _ y⟩ : Join.Simplex A B n) = _
    rw [hx, hy]

/-- 概要：左右両方の部分複体の join は、左右の join の交わりと同型。
方針：単射の像への同型を、像と交わりの等式で移送する。
規約：同型の向きは join から交わりへ。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の pushout。 -/
noncomputable def joinIntersectionIso {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    join (A₀ : SSet.{u}) (B₀ : SSet.{u}) ≅
      ((joinSubcomplexLeft A₀ B ⊓ joinSubcomplexRight A B₀ :
        (join A B).Subcomplex) : SSet.{u}) := by
  letI : Mono (joinMap A₀.ι B₀.ι) := joinMap_mono _ _
  letI := Subfunctor.instIsIsoFunctorTypeToRangeOfMono (joinMap A₀.ι B₀.ι)
  exact asIso (Subfunctor.toRange (joinMap A₀.ι B₀.ι)) ≪≫
    Subcomplex.eqToIso (joinMap_range_inf A₀ B₀)

/-- 概要：交わりの同型は周囲の join への包含と可換。
方針：像の同型と等式による同型の構成を計算する。
規約：合成は包含を最後に適用する順。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の pushout の比較。 -/
lemma joinIntersectionIso_hom_ι {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    (joinIntersectionIso A₀ B₀).hom ≫
      (joinSubcomplexLeft A₀ B ⊓ joinSubcomplexRight A B₀).ι = joinMap A₀.ι B₀.ι := by
  simp [joinIntersectionIso]

/-- 概要：左部分複体の join から pushout-join の始域への射。
方針：joinMap を像の和の部分複体へ制限する。
規約：始域は A₀⋆B。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の貼り合わせ。 -/
def joinUnionLeft {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    join (A₀ : SSet.{u}) B ⟶ (joinUnion A₀ B₀ : SSet.{u}) :=
  (joinUnion A₀ B₀).lift (joinMap A₀.ι (𝟙 B)) le_sup_left

/-- 概要：右部分複体の join から pushout-join の始域への射。
方針：joinMap を像の和の部分複体へ制限する。
規約：始域は A⋆B₀。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の貼り合わせ。 -/
def joinUnionRight {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    join A (B₀ : SSet.{u}) ⟶ (joinUnion A₀ B₀ : SSet.{u}) :=
  (joinUnion A₀ B₀).lift (joinMap (𝟙 A) B₀.ι) le_sup_right

/-- 概要：join の和は二つの join を共通部分に沿って貼り合わせた pushout。
方針：部分複体の交わりと和の双カルテジアン正方形を同型で移送する。
規約：上辺は右因子の包含、左辺は左因子の包含。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の持ち上げ問題の結合。 -/
@[kerodon 018H]
lemma joinUnion_isPushout {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    IsPushout (joinMap (𝟙 (A₀ : SSet.{u})) B₀.ι)
      (joinMap A₀.ι (𝟙 (B₀ : SSet.{u}))) (joinUnionLeft A₀ B₀) (joinUnionRight A₀ B₀) := by
  have hs : Subcomplex.BicartSq
      (joinSubcomplexLeft A₀ B ⊓ joinSubcomplexRight A B₀)
      (joinSubcomplexLeft A₀ B) (joinSubcomplexRight A B₀) (joinUnion A₀ B₀) :=
    { sup_eq := rfl, inf_eq := rfl }
  apply hs.isPushout.of_iso' (joinIntersectionIso A₀ B₀)
    (joinSubcomplexLeftIso A₀ B) (joinSubcomplexRightIso A B₀) (Iso.refl _)
  · apply (cancel_mono (joinSubcomplexLeft A₀ B).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinIntersectionIso_hom_ι,
      joinSubcomplexLeftIso_hom_ι]
    rw [← joinMap_comp]
    simp
  · apply (cancel_mono (joinSubcomplexRight A B₀).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinIntersectionIso_hom_ι,
      joinSubcomplexRightIso_hom_ι]
    rw [← joinMap_comp]
    simp
  · apply (cancel_mono (joinUnion A₀ B₀).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, Iso.refl_hom,
      Category.comp_id, joinSubcomplexLeftIso_hom_ι, joinUnionLeft, Subcomplex.lift_ι]
  · apply (cancel_mono (joinUnion A₀ B₀).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, Iso.refl_hom,
      Category.comp_id, joinSubcomplexRightIso_hom_ι, joinUnionRight, Subcomplex.lift_ι]

/-- 概要：pushout-join の左射と周囲への包含の合成は元の joinMap。
方針：部分複体への制限の定義を使う。
規約：A₀⋆B の側。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の持ち上げの移送。 -/
lemma joinUnionLeft_ι {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    joinUnionLeft A₀ B₀ ≫ (joinUnion A₀ B₀).ι = joinMap A₀.ι (𝟙 B) := rfl

/-- 概要：pushout-join の右射と周囲への包含の合成は元の joinMap。
方針：部分複体への制限の定義を使う。
規約：A⋆B₀ の側。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の持ち上げの移送。 -/
lemma joinUnionRight_ι {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    joinUnionRight A₀ B₀ ≫ (joinUnion A₀ B₀).ι = joinMap (𝟙 A) B₀.ι := rfl

/-- 概要：coslice への二つの射は uncurry が等しければ等しい。
方針：普遍性の同値の単射性を使う。
規約：固定された図式 p は共通。
使われ方：HTT §2.1.2、Kerodon §4.3.6 の持ち上げの比較。 -/
lemma sliceUnderUncurry_injective {A K X : SSet.{u}} (p : K ⟶ X) :
    Function.Injective (sliceUnderUncurry (A := A) (p := p)) := by
  intro f g h
  exact (sliceUnderEquiv p).injective (Subtype.ext h)

/-- 概要：図式の制限と標的の射の相対 coslice を表す pullback。
方針：Y 側の錐と K₀ 上の X 側の錐が同じ Y 側の制限を持つ条件を課す。
規約：p:K→X、f:K₀→K、q:X→Y。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の生成セルからの閉包。 -/
noncomputable def relativeSliceUnder {K₀ K X Y : SSet.{u}}
    (p : K ⟶ X) (f : K₀ ⟶ K) (q : X ⟶ Y) : SSet.{u} :=
  pullback (sliceUnderRestrict (p ≫ q) f) (sliceUnderPostcomp (f ≫ p) q)

/-- 概要：coslice から相対 coslice への比較射。
方針：標的の射で写した錐と図式を制限した錐を組にする。
規約：pullback の第一成分が Y 側、第二成分が K₀ 上の X 側。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の corner の持ち上げ。 -/
noncomputable def relativeSliceUnderMap {K₀ K X Y : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) (q : X ⟶ Y) :
    sliceUnder p ⟶ relativeSliceUnder p f q :=
  pullback.lift (sliceUnderPostcomp p q) (sliceUnderRestrict p f)
    (sliceUnderRestrict_postcomp p f q)

/-- 概要：pushout-join の持ち上げ性は相対 coslice の持ち上げ性を与える。
方針：三つの錐を uncurry し、pushout で貼り合わせ、得た持ち上げを curry する。
規約：右側の射は部分複体の包含、左側も部分複体の包含。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の境界セルから全単射への移送。 -/
lemma relativeSliceUnderMap_hasLiftingProperty {A B X Y : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (q : X ⟶ Y)
    (h : HasLiftingProperty (joinUnion A₀ B₀).ι q) (p : A ⟶ X) :
    HasLiftingProperty B₀.ι (relativeSliceUnderMap p A₀.ι q) := by
  constructor
  intro a b sq
  let s := sliceUnderRestrict (p ≫ q) A₀.ι
  let t := sliceUnderPostcomp (A₀.ι ≫ p) q
  let F := sliceUnderUncurry (b ≫ pullback.fst s t)
  let G := sliceUnderUncurry (b ≫ pullback.snd s t)
  let H := sliceUnderUncurry a
  have ha : a ≫ sliceUnderRestrict p A₀.ι = B₀.ι ≫ (b ≫ pullback.snd s t) := by
    have hh := congrArg (fun z ↦ z ≫ pullback.snd s t) sq.w
    simpa only [Category.assoc, relativeSliceUnderMap, s, t, pullback.lift_snd] using hh
  have ha' : a ≫ sliceUnderPostcomp p q = B₀.ι ≫ (b ≫ pullback.fst s t) := by
    have hh := congrArg (fun z ↦ z ≫ pullback.fst s t) sq.w
    simpa only [Category.assoc, relativeSliceUnderMap, s, t, pullback.lift_fst] using hh
  have hb : (b ≫ pullback.fst s t) ≫ sliceUnderRestrict (p ≫ q) A₀.ι =
      (b ≫ pullback.snd s t) ≫ sliceUnderPostcomp (A₀.ι ≫ p) q := by
    simpa only [Category.assoc] using
      congrArg (fun z ↦ b ≫ z) (pullback.condition (f := s) (g := t))
  have hover : joinMap (𝟙 (A₀ : SSet.{u})) B₀.ι ≫ G =
      joinMap A₀.ι (𝟙 (B₀ : SSet.{u})) ≫ H := by
    change _ = joinMap A₀.ι (𝟙 _) ≫ sliceUnderUncurry a
    rw [← sliceUnderUncurry_restrict, ha, sliceUnderUncurry_precomp]
  let hs := joinUnion_isPushout A₀ B₀
  let T := hs.desc G H hover
  have hG : G ≫ q = joinMap A₀.ι (𝟙 B) ≫ F := by
    have hh := congrArg sliceUnderUncurry hb
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_postcomp] at hh
    exact hh.symm
  have hH : H ≫ q = joinMap (𝟙 A) B₀.ι ≫ F := by
    have hh := congrArg sliceUnderUncurry ha'
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at hh
    exact hh
  have hT : CommSq T (joinUnion A₀ B₀).ι q F := by
    constructor
    apply hs.hom_ext
    · dsimp [T]
      rw [← Category.assoc, hs.inl_desc]
      rw [← Category.assoc, joinUnionLeft_ι]
      exact hG
    · dsimp [T]
      rw [← Category.assoc, hs.inr_desc]
      rw [← Category.assoc, joinUnionRight_ι]
      exact hH
  have := h
  let L := hT.lift
  have hleft : joinMap A₀.ι (𝟙 B) ≫ L = G := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft A₀ B₀ ≫ ((joinUnion A₀ B₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inl_desc G H hover
  have hright : joinMap (𝟙 A) B₀.ι ≫ L = H := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight A₀ B₀ ≫ ((joinUnion A₀ B₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inr_desc G H hover
  have hfixed : joinInl A B ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInl A (B₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hright
  · apply pullback.hom_ext
    · simp only [Category.assoc, relativeSliceUnderMap, pullback.lift_fst]
      apply sliceUnderUncurry_injective (p ≫ q)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
      exact hT.fac_right
    · simp only [Category.assoc, relativeSliceUnderMap, pullback.lift_snd]
      apply sliceUnderUncurry_injective (A₀.ι ≫ p)
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
      exact hleft

/-- 概要：相対 coslice の持ち上げ性から pushout-join の持ち上げ性を復元する。
方針：左端の図式を固定し、与えられた正方形を curry して持ち上げた後 uncurry する。
規約：固定図式 p の全てについて相対 coslice の持ち上げ性を仮定する。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の境界セルから全単射への移送。 -/
lemma joinUnion_hasLiftingProperty_of_relativeSliceUnderMap {A B X Y : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (q : X ⟶ Y)
    (h : ∀ p : A ⟶ X, HasLiftingProperty B₀.ι (relativeSliceUnderMap p A₀.ι q)) :
    HasLiftingProperty (joinUnion A₀ B₀).ι q := by
  constructor
  intro a b sq
  let G := joinUnionLeft A₀ B₀ ≫ a
  let H := joinUnionRight A₀ B₀ ≫ a
  let p := joinInl A (B₀ : SSet.{u}) ≫ H
  have hpure : joinInl (A₀ : SSet.{u}) B ≫ joinUnionLeft A₀ B₀ =
      A₀.ι ≫ joinInl A (B₀ : SSet.{u}) ≫ joinUnionRight A₀ B₀ := by
    apply (cancel_mono (joinUnion A₀ B₀).ι).1
    simp only [Category.assoc, joinUnionLeft_ι, joinUnionRight_ι]
    rw [joinInl_joinMap, joinInl_joinMap, Category.id_comp]
  have hG : joinInl (A₀ : SSet.{u}) B ≫ G = A₀.ι ≫ p := by
    dsimp [G, p, H]
    rw [← Category.assoc, hpure]
    simp only [Category.assoc]
  have hH : joinInl A (B₀ : SSet.{u}) ≫ H = p := rfl
  have hGq : G ≫ q = joinMap A₀.ι (𝟙 B) ≫ b := by
    dsimp [G]
    rw [Category.assoc, sq.w, ← Category.assoc, joinUnionLeft_ι]
  have hHq : H ≫ q = joinMap (𝟙 A) B₀.ι ≫ b := by
    dsimp [H]
    rw [Category.assoc, sq.w, ← Category.assoc, joinUnionRight_ι]
  have hF : joinInl A B ≫ b = p ≫ q := by
    calc
      _ = joinInl A (B₀ : SSet.{u}) ≫ (joinMap (𝟙 A) B₀.ι ≫ b) := by
        rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
      _ = joinInl A (B₀ : SSet.{u}) ≫ (H ≫ q) := by rw [hHq]
      _ = p ≫ q := (Category.assoc _ _ _).symm
  let hs := joinUnion_isPushout A₀ B₀
  have hover : joinMap (𝟙 (A₀ : SSet.{u})) B₀.ι ≫ G =
      joinMap A₀.ι (𝟙 (B₀ : SSet.{u})) ≫ H := by
    dsimp [G, H]
    rw [← Category.assoc, ← Category.assoc, hs.w]
  let s := sliceUnderRestrict (p ≫ q) A₀.ι
  let t := sliceUnderPostcomp (A₀.ι ≫ p) q
  have hc : sliceUnderCurry b hF ≫ s = sliceUnderCurry G hG ≫ t := by
    apply sliceUnderUncurry_injective (A₀.ι ≫ p ≫ q)
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_postcomp,
      sliceUnderUncurry_curry, sliceUnderUncurry_curry]
    exact hGq.symm
  let v : B ⟶ relativeSliceUnder p A₀.ι q :=
    pullback.lift (sliceUnderCurry b hF) (sliceUnderCurry G hG) hc
  have hv : CommSq (sliceUnderCurry H hH) B₀.ι (relativeSliceUnderMap p A₀.ι q) v := by
    constructor
    apply pullback.hom_ext
    · dsimp [v, relativeSliceUnderMap]
      simp only [Category.assoc, s, t, pullback.lift_fst]
      apply sliceUnderUncurry_injective (p ≫ q)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp,
        sliceUnderUncurry_curry, sliceUnderUncurry_curry]
      exact hHq
    · dsimp [v, relativeSliceUnderMap]
      simp only [Category.assoc, s, t, pullback.lift_snd]
      apply sliceUnderUncurry_injective (A₀.ι ≫ p)
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp,
        sliceUnderUncurry_curry, sliceUnderUncurry_curry]
      exact hover.symm
  have := h p
  let c := hv.lift
  have hleft : joinMap A₀.ι (𝟙 B) ≫ sliceUnderUncurry c = G := by
    have hh := congrArg (fun z ↦ z ≫ pullback.snd s t) hv.fac_right
    simp only [Category.assoc, relativeSliceUnderMap, s, t, v, pullback.lift_snd] at hh
    have he := congrArg sliceUnderUncurry hh
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry] at he
    exact he
  have hright : joinMap (𝟙 A) B₀.ι ≫ sliceUnderUncurry c = H := by
    have he := congrArg sliceUnderUncurry hv.fac_left
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry] at he
    exact he
  refine CommSq.HasLift.mk' { l := sliceUnderUncurry c, fac_left := ?_, fac_right := ?_ }
  · apply hs.hom_ext
    · rw [← Category.assoc, joinUnionLeft_ι]
      exact hleft
    · rw [← Category.assoc, joinUnionRight_ι]
      exact hright
  · have hh := congrArg (fun z ↦ z ≫ pullback.fst s t) hv.fac_right
    simp only [Category.assoc, relativeSliceUnderMap, s, t, v, pullback.lift_fst] at hh
    have he := congrArg sliceUnderUncurry hh
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry] at he
    exact he

/-- 概要：右ホーンと任意の部分複体包含の pushout-join は inner anodyne。
方針：相対 coslice の射が全境界に対し持ち上げ性を持つことから、境界セル分解で全単射へ広げる。
規約：左因子は正次元の右ホーン、右因子は任意の部分複体。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の第一の閉包段階。 -/
lemma joinUnion_rightHorn_innerAnodyne {B : SSet.{u}} (B₀ : B.Subcomplex)
    (n : ℕ) (i : Fin (n + 2)) (h0 : 0 < i) :
    innerAnodyneExtensions (joinUnion (horn (n + 1) i) B₀).ι := by
  intro X Y q hq
  apply joinUnion_hasLiftingProperty_of_relativeSliceUnderMap
  intro p
  have hc : SSet.modelCategoryQuillen.I.rlp
      (relativeSliceUnderMap p (horn (n + 1) i).ι q) := by
    intro C D g hg
    cases hg with
    | mk r =>
      exact relativeSliceUnderMap_hasLiftingProperty _ _ q
        (joinUnion_rightHorn_boundary_innerAnodyne n r i h0 q hq) p
  have hm : (monomorphisms SSet.{u}).rlp
      (relativeSliceUnderMap p (horn (n + 1) i).ι q) := by
    rw [SSet.rlp_monomorphisms]
    exact hc
  exact hm B₀.ι inferInstance

/-- 概要：slice への二つの射は uncurry が等しければ等しい。
方針：普遍性の同値の単射性を使う。
規約：固定された図式 p は共通。
使われ方：HTT §2.1.2、Kerodon §4.3.6 の持ち上げの比較。 -/
lemma sliceOverUncurry_injective {A K X : SSet.{u}} (p : K ⟶ X) :
    Function.Injective (sliceOverUncurry (A := A) (p := p)) := by
  intro f g h
  exact (sliceOverEquiv p).injective (Subtype.ext h)

/-- 概要：図式の制限と標的の射の相対 slice を表す pullback。
方針：Y 側の錐と K₀ 上の X 側の錐が同じ Y 側の制限を持つ条件を課す。
規約：p:K→X、f:K₀→K、q:X→Y。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の生成セルからの閉包。 -/
noncomputable def relativeSliceOver {K₀ K X Y : SSet.{u}}
    (p : K ⟶ X) (f : K₀ ⟶ K) (q : X ⟶ Y) : SSet.{u} :=
  pullback (sliceOverRestrict (p ≫ q) f) (sliceOverPostcomp (f ≫ p) q)

/-- 概要：slice から相対 slice への比較射。
方針：標的の射で写した錐と図式を制限した錐を組にする。
規約：pullback の第一成分が Y 側、第二成分が K₀ 上の X 側。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の corner の持ち上げ。 -/
noncomputable def relativeSliceOverMap {K₀ K X Y : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) (q : X ⟶ Y) :
    sliceOver p ⟶ relativeSliceOver p f q :=
  pullback.lift (sliceOverPostcomp p q) (sliceOverRestrict p f)
    (sliceOverRestrict_postcomp p f q)

/-- 概要：pushout-join の持ち上げ性は相対 slice の持ち上げ性を与える。
方針：三つの錐を uncurry し、pushout で貼り合わせ、得た持ち上げを curry する。
規約：右側の射は部分複体の包含、左側も部分複体の包含。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の境界セルから全単射への移送。 -/
lemma relativeSliceOverMap_hasLiftingProperty {A B X Y : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (q : X ⟶ Y)
    (h : HasLiftingProperty (joinUnion B₀ A₀).ι q) (p : A ⟶ X) :
    HasLiftingProperty B₀.ι (relativeSliceOverMap p A₀.ι q) := by
  constructor
  intro a b sq
  let s := sliceOverRestrict (p ≫ q) A₀.ι
  let t := sliceOverPostcomp (A₀.ι ≫ p) q
  let F := sliceOverUncurry (b ≫ pullback.fst s t)
  let G := sliceOverUncurry (b ≫ pullback.snd s t)
  let H := sliceOverUncurry a
  have ha : a ≫ sliceOverRestrict p A₀.ι = B₀.ι ≫ (b ≫ pullback.snd s t) := by
    have hh := congrArg (fun z ↦ z ≫ pullback.snd s t) sq.w
    simpa only [Category.assoc, relativeSliceOverMap, s, t, pullback.lift_snd] using hh
  have ha' : a ≫ sliceOverPostcomp p q = B₀.ι ≫ (b ≫ pullback.fst s t) := by
    have hh := congrArg (fun z ↦ z ≫ pullback.fst s t) sq.w
    simpa only [Category.assoc, relativeSliceOverMap, s, t, pullback.lift_fst] using hh
  have hb : (b ≫ pullback.fst s t) ≫ sliceOverRestrict (p ≫ q) A₀.ι =
      (b ≫ pullback.snd s t) ≫ sliceOverPostcomp (A₀.ι ≫ p) q := by
    simpa only [Category.assoc] using
      congrArg (fun z ↦ b ≫ z) (pullback.condition (f := s) (g := t))
  have hover : joinMap B₀.ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 (B₀ : SSet.{u})) A₀.ι ≫ H := by
    change _ = joinMap (𝟙 _) A₀.ι ≫ sliceOverUncurry a
    rw [← sliceOverUncurry_restrict, ha, sliceOverUncurry_precomp]
  let hs := (joinUnion_isPushout B₀ A₀).flip
  let T := hs.desc G H hover
  have hG : G ≫ q = joinMap (𝟙 B) A₀.ι ≫ F := by
    have hh := congrArg sliceOverUncurry hb
    rw [sliceOverUncurry_restrict, sliceOverUncurry_postcomp] at hh
    exact hh.symm
  have hH : H ≫ q = joinMap B₀.ι (𝟙 A) ≫ F := by
    have hh := congrArg sliceOverUncurry ha'
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_precomp] at hh
    exact hh
  have hT : CommSq T (joinUnion B₀ A₀).ι q F := by
    constructor
    apply hs.hom_ext
    · dsimp [T]
      rw [← Category.assoc, hs.inl_desc]
      rw [← Category.assoc, joinUnionRight_ι]
      exact hG
    · dsimp [T]
      rw [← Category.assoc, hs.inr_desc]
      rw [← Category.assoc, joinUnionLeft_ι]
      exact hH
  have := h
  let L := hT.lift
  have hleft : joinMap (𝟙 B) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight B₀ A₀ ≫ ((joinUnion B₀ A₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inl_desc G H hover
  have hright : joinMap B₀.ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft B₀ A₀ ≫ ((joinUnion B₀ A₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inr_desc G H hover
  have hfixed : joinInr B A ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInr (B₀ : SSet.{u}) A ≫ z) hright
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceOverCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceOverUncurry_injective p
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact hright
  · apply pullback.hom_ext
    · simp only [Category.assoc, relativeSliceOverMap, pullback.lift_fst]
      apply sliceOverUncurry_injective (p ≫ q)
      rw [sliceOverUncurry_postcomp, sliceOverUncurry_curry]
      exact hT.fac_right
    · simp only [Category.assoc, relativeSliceOverMap, pullback.lift_snd]
      apply sliceOverUncurry_injective (A₀.ι ≫ p)
      rw [sliceOverUncurry_restrict, sliceOverUncurry_curry]
      exact hleft

/-- 概要：相対 slice の持ち上げ性から pushout-join の持ち上げ性を復元する。
方針：右端の図式を固定し、与えられた正方形を curry して持ち上げた後 uncurry する。
規約：固定図式 p の全てについて相対 slice の持ち上げ性を仮定する。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6 の境界セルから全単射への移送。 -/
lemma joinUnion_hasLiftingProperty_of_relativeSliceOverMap {A B X Y : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (q : X ⟶ Y)
    (h : ∀ p : A ⟶ X, HasLiftingProperty B₀.ι (relativeSliceOverMap p A₀.ι q)) :
    HasLiftingProperty (joinUnion B₀ A₀).ι q := by
  constructor
  intro a b sq
  let G := joinUnionRight B₀ A₀ ≫ a
  let H := joinUnionLeft B₀ A₀ ≫ a
  let p := joinInr (B₀ : SSet.{u}) A ≫ H
  have hpure : joinInr B (A₀ : SSet.{u}) ≫ joinUnionRight B₀ A₀ =
      A₀.ι ≫ joinInr (B₀ : SSet.{u}) A ≫ joinUnionLeft B₀ A₀ := by
    apply (cancel_mono (joinUnion B₀ A₀).ι).1
    simp only [Category.assoc, joinUnionRight_ι, joinUnionLeft_ι]
    rw [joinInr_joinMap, joinInr_joinMap, Category.id_comp]
  have hG : joinInr B (A₀ : SSet.{u}) ≫ G = A₀.ι ≫ p := by
    dsimp [G, p, H]
    rw [← Category.assoc, hpure]
    simp only [Category.assoc]
  have hH : joinInr (B₀ : SSet.{u}) A ≫ H = p := rfl
  have hGq : G ≫ q = joinMap (𝟙 B) A₀.ι ≫ b := by
    dsimp [G]
    rw [Category.assoc, sq.w, ← Category.assoc, joinUnionRight_ι]
  have hHq : H ≫ q = joinMap B₀.ι (𝟙 A) ≫ b := by
    dsimp [H]
    rw [Category.assoc, sq.w, ← Category.assoc, joinUnionLeft_ι]
  have hF : joinInr B A ≫ b = p ≫ q := by
    calc
      _ = joinInr (B₀ : SSet.{u}) A ≫ (joinMap B₀.ι (𝟙 A) ≫ b) := by
        rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
      _ = joinInr (B₀ : SSet.{u}) A ≫ (H ≫ q) := by rw [hHq]
      _ = p ≫ q := (Category.assoc _ _ _).symm
  let hs := (joinUnion_isPushout B₀ A₀).flip
  have hover : joinMap B₀.ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 (B₀ : SSet.{u})) A₀.ι ≫ H := by
    dsimp [G, H]
    rw [← Category.assoc, ← Category.assoc, hs.w]
  let s := sliceOverRestrict (p ≫ q) A₀.ι
  let t := sliceOverPostcomp (A₀.ι ≫ p) q
  have hc : sliceOverCurry b hF ≫ s = sliceOverCurry G hG ≫ t := by
    apply sliceOverUncurry_injective (A₀.ι ≫ p ≫ q)
    rw [sliceOverUncurry_restrict, sliceOverUncurry_postcomp,
      sliceOverUncurry_curry, sliceOverUncurry_curry]
    exact hGq.symm
  let v : B ⟶ relativeSliceOver p A₀.ι q :=
    pullback.lift (sliceOverCurry b hF) (sliceOverCurry G hG) hc
  have hv : CommSq (sliceOverCurry H hH) B₀.ι (relativeSliceOverMap p A₀.ι q) v := by
    constructor
    apply pullback.hom_ext
    · dsimp [v, relativeSliceOverMap]
      simp only [Category.assoc, s, t, pullback.lift_fst]
      apply sliceOverUncurry_injective (p ≫ q)
      rw [sliceOverUncurry_postcomp, sliceOverUncurry_precomp,
        sliceOverUncurry_curry, sliceOverUncurry_curry]
      exact hHq
    · dsimp [v, relativeSliceOverMap]
      simp only [Category.assoc, s, t, pullback.lift_snd]
      apply sliceOverUncurry_injective (A₀.ι ≫ p)
      rw [sliceOverUncurry_restrict, sliceOverUncurry_precomp,
        sliceOverUncurry_curry, sliceOverUncurry_curry]
      exact hover.symm
  have := h p
  let c := hv.lift
  have hleft : joinMap (𝟙 B) A₀.ι ≫ sliceOverUncurry c = G := by
    have hh := congrArg (fun z ↦ z ≫ pullback.snd s t) hv.fac_right
    simp only [Category.assoc, relativeSliceOverMap, s, t, v, pullback.lift_snd] at hh
    have he := congrArg sliceOverUncurry hh
    rw [sliceOverUncurry_restrict, sliceOverUncurry_curry] at he
    exact he
  have hright : joinMap B₀.ι (𝟙 A) ≫ sliceOverUncurry c = H := by
    have he := congrArg sliceOverUncurry hv.fac_left
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry] at he
    exact he
  refine CommSq.HasLift.mk' { l := sliceOverUncurry c, fac_left := ?_, fac_right := ?_ }
  · apply hs.hom_ext
    · rw [← Category.assoc, joinUnionRight_ι]
      exact hleft
    · rw [← Category.assoc, joinUnionLeft_ι]
      exact hright
  · have hh := congrArg (fun z ↦ z ≫ pullback.fst s t) hv.fac_right
    simp only [Category.assoc, relativeSliceOverMap, s, t, v, pullback.lift_fst] at hh
    have he := congrArg sliceOverUncurry hh
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_curry] at he
    exact he

/-- 概要：任意の部分複体包含と左ホーンの pushout-join は inner anodyne。
方針：相対 slice の射の境界持ち上げ性を、単射の境界セル分解で全単射へ広げる。
規約：右因子は正次元の左ホーン、左因子は任意の部分複体。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の第二の閉包段階。 -/
lemma joinUnion_leftHorn_innerAnodyne {A : SSet.{u}} (A₀ : A.Subcomplex)
    (n : ℕ) (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
    innerAnodyneExtensions (joinUnion A₀ (horn (n + 1) i)).ι := by
  intro X Y q hq
  apply joinUnion_hasLiftingProperty_of_relativeSliceOverMap
  intro p
  have hc : SSet.modelCategoryQuillen.I.rlp
      (relativeSliceOverMap p (horn (n + 1) i).ι q) := by
    intro C D g hg
    cases hg with
    | mk r =>
      exact relativeSliceOverMap_hasLiftingProperty _ _ q
        (joinUnion_boundary_leftHorn_innerAnodyne r n i hn q hq) p
  have hm : (monomorphisms SSet.{u}).rlp
      (relativeSliceOverMap p (horn (n + 1) i).ι q) := by
    rw [SSet.rlp_monomorphisms]
    exact hc
  exact hm A₀.ι inferInstance

end SerrePositivity.InfinityCategories
