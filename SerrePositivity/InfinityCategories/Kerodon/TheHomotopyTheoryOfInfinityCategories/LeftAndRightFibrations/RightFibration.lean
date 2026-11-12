module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAnodyne
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左右のファイブレーションと、slice 射影の右ファイブレーション性。
方針：左右のホーンの rlp を定義し、pushout-join の内 anodyne 性で錐を延長する。
規約：右ホーンは零番目以外、左ホーンは最後以外を許す。
使われ方：HTT Proposition 2.1.2.1–2.1.2.2、Kerodon §4.3.6（Tag 018E） の slice の quasicategory 性。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：右ファイブレーションは正の添字のホーンの rlp を持つ射。
方針：ホーンの族の右持ち上げ性として定義する。
規約：最後のホーンも含む。
使われ方：HTT Definition 2.0.0.3、Proposition 2.1.2.1 の slice 射影。 -/
def rightFibrations : MorphismProperty SSet.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange, IsStableUnderRetracts

/-- 概要：左ファイブレーションは最後以外のホーンの rlp を持つ射。
方針：ホーンの族の右持ち上げ性として定義する。
規約：零番目のホーンも含む。
使われ方：HTT Definition 2.0.0.3、Proposition 2.1.2.2 の双対的な射影。 -/
@[kerodon 00T9]
def leftFibrations : MorphismProperty SSet.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange, IsStableUnderRetracts

/-- 概要：右ファイブレーション性を型クラスとして表す。
方針：rightFibrations への所属を保持する。
規約：追加の構造や充填の選択は持たない。
使われ方：HTT §2.1.2 の slice の型クラスへの接続。 -/
@[kerodon 00T9]
class RightFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : rightFibrations p

/-- 概要：左ファイブレーション性を型クラスとして表す。
方針：leftFibrations への所属を保持する。
規約：追加の構造や充填の選択は持たない。
使われ方：HTT §2.1.2 の coslice の型クラスへの接続。 -/
@[kerodon 00T9, kerodon 014X]
class LeftFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : leftFibrations p

/-- 概要：右ファイブレーションは inner fibration。
方針：内ホーンは右ホーンの特別な場合である。
規約：標的が quasicategory であることは不要。
使われ方：HTT §2.1.2、Mathlib の quasicategory_of_innerFibration への接続。 -/
instance rightFibration_innerFibration {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    InnerFibration p where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i h0 hn => exact RightFibration.mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro i h0)

/-- 概要：左ファイブレーションは inner fibration。
方針：内ホーンは左ホーンの特別な場合である。
規約：標的が quasicategory であることは不要。
使われ方：HTT §2.1.2、Mathlib の quasicategory_of_innerFibration への接続。 -/
instance leftFibration_innerFibration {X Y : SSet.{u}} (p : X ⟶ Y) [LeftFibration p] :
    InnerFibration p where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i h0 hn => exact LeftFibration.mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hn)

/-- 概要：任意の K の空部分複体との右 join は左因子と同型。
方針：右区間が非空なら空部分複体の単体は存在せず、左包含だけが残る。
規約：逆射は joinInl である。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.6（Tag 018E） の射影の充填問題。 -/
noncomputable def joinEmptyIso (A K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A ((⊥ : K.Subcomplex) : SSet.{u}) ≅ A := by
  let E : SSet.{u} := (⊥ : K.Subcomplex)
  haveI (r : ℕ) : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj E r) := by
    cases r with
    | zero => change Subsingleton PUnit; infer_instance
    | succ r => exact ⟨fun x _ ↦ False.elim x.property⟩
  haveI : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A E) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    rw [isIso_iff_bijective]
    constructor
    · intro x y h
      exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h).2)
    · intro s
      have hr : n.unop.len + 1 - s.1.val = 0 := by
        by_contra h
        obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero h
        have y := cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj E) hr) s.2.2
        exact y.property
      have hc : s.1.val = n.unop.len + 1 := by have := s.1.isLt; omega
      rcases s with ⟨⟨ℓ, hℓ⟩, x, y⟩
      dsimp only at hc
      subst ℓ
      refine ⟨x, ?_⟩
      refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
      · rfl
      · rfl
      · exact Subsingleton.elim _ _
  exact (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A E)).symm

/-- 概要：空の右 join の同型の逆射は左包含。
方針：同型の定義を展開する。
規約：空因子は K の空部分複体。
使われ方：HTT §1.2.8・2.1.2 の射影の持ち上げ。 -/
lemma joinEmptyIso_inv (A K : SSet.{u}) :
    (joinEmptyIso A K).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A ((⊥ : K.Subcomplex) : SSet.{u}) := rfl

/-- 概要：空の右 join の単位同型は左因子の射に自然。
方針：左包含の自然性を同型の逆射で打ち消す。
規約：空因子を共通に固定する。
使われ方：HTT §1.2.8・2.1.2 の錐の貼り合わせ。 -/
lemma joinEmptyIso_naturality {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 ((⊥ : K.Subcomplex) : SSet.{u})) ≫ (joinEmptyIso B K).hom =
      (joinEmptyIso A K).hom ≫ f := by
  apply (cancel_epi (joinEmptyIso A K).inv).1
  rw [← Category.assoc, joinEmptyIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
  simp only [Category.assoc, ← joinEmptyIso_inv, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

/-- 概要：slice の curry の射影は元の join からの射の左制限。
方針：Yoneda の同値の単射性と左包含の自然性を使う。
規約：任意の A に対して成り立ち、quasicategory の仮定は不要。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の射影の持ち上げ問題。 -/
lemma sliceOverCurry_projection {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K ≫ F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n.unop) K ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ F)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K ≫ F).app n a
  apply SSet.yonedaEquiv.symm.injective
  rw [Equiv.symm_apply_apply, ← SSet.yonedaEquiv_symm_comp,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc]

/-- 概要：slice への射を uncurry した錐の左制限は射影との合成。
方針：普遍性の逆関係を curry の射影の式に適用する。
規約：任意の A に対して成り立つ。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の射影の持ち上げ問題。 -/
lemma sliceOverUncurry_projection {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p := by
  have h := sliceOverCurry_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed f)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry_uncurry] at h
  exact h.symm

/-- 概要：quasicategory の slice 射影は right anodyne な部分複体包含に対し持ち上げ性を持つ。
方針：錐と射影の値を空部分複体との pushout-join 上で貼り合わせ、内 anodyne 性で延長する。
規約：図式 K→X と試験する部分複体 A₀⊆A は任意。
使われ方：HTT Proposition 2.1.2.1、Kerodon §4.3.6（Tag 018E） の右ファイブレーション性。 -/
lemma sliceOverProjection_hasLiftingProperty {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions A₀.ι) :
    HasLiftingProperty A₀.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) := by
  constructor
  intro a b sq
  let E : SSet.{u} := (⊥ : K.Subcomplex)
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a
  let H := (joinEmptyIso A K).hom ≫ b
  have hover : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (A₀ : SSet.{u})) (⊥ : K.Subcomplex).ι ≫ G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap A₀.ι (𝟙 E) ≫ H := by
    apply (cancel_epi (joinEmptyIso (A₀ : SSet.{u}) K).inv).1
    rw [← Category.assoc, joinEmptyIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (A₀ : SSet.{u}) K ≫ G =
      A₀.ι ≫ ((joinEmptyIso A K).inv ≫ ((joinEmptyIso A K).hom ≫ b))
    rw [Iso.inv_hom_id_assoc, sliceOverUncurry_projection]
    exact sq.w
  let hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout A₀ (⊥ : K.Subcomplex)
  let T := hs.desc G H hover
  have hT : CommSq T (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion A₀ (⊥ : K.Subcomplex)).ι (terminal.from X)
      (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K)) := ⟨terminal.hom_ext _ _⟩
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_rightAnodyne A₀ (⊥ : K.Subcomplex) hA
    (terminal.from X) InnerFibration.mem
  let L := hT.lift
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap A₀.ι (𝟙 K) ≫ L = G := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι, Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft A₀ (⊥ : K.Subcomplex) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion A₀ (⊥ : K.Subcomplex)).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inl_desc G H hover
  have hright : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (⊥ : K.Subcomplex).ι ≫ L = H := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι, Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight A₀ (⊥ : K.Subcomplex) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion A₀ (⊥ : K.Subcomplex)).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inr_desc G H hover
  have hfixed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ L = p := by
    have hh := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (A₀ : SSet.{u}) K ≫ z) hleft
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp] at hh
    exact hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective p
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry]
    exact hleft
  · rw [sliceOverCurry_projection]
    have hh := congrArg (fun z ↦ (joinEmptyIso A K).inv ≫ z) hright
    rw [← Category.assoc, joinEmptyIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (by dsimp [H]; rw [← joinEmptyIso_inv, Iso.inv_hom_id_assoc])

/-- 概要：quasicategory の任意の図式上の slice 射影は右ファイブレーション。
方針：右ホーン包含の right anodyne 性と射影の持ち上げ補題を使う。
規約：K の有限性等の追加仮定はない。
使われ方：HTT Proposition 2.1.2.1、Kerodon §4.3.6（Tag 018E） の slice の一般論。 -/
@[kerodon 018F]
instance sliceOverProjection_rightFibration {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i h0 =>
      exact sliceOverProjection_hasLiftingProperty p _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn i h0)

/-- 概要：quasicategory の任意の図式上の slice は quasicategory。
方針：射影は右ファイブレーション、従って inner fibration である。
規約：Mathlib の quasicategory_of_innerFibration を適用する。
使われ方：HTT Proposition 2.1.2.1、極限を slice の終対象として定義する基盤。 -/
@[kerodon 018F]
instance sliceOver_quasicategory {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)

/-- 概要：空の左 join の同型の逆射は右包含。
方針：同型の定義を展開する。
規約：空因子は K の空部分複体。
使われ方：HTT §1.2.8・2.1.2 の coslice 射影の持ち上げ。 -/
lemma emptyJoinIso_inv (K A : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K A).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((⊥ : K.Subcomplex) : SSet.{u}) A := rfl

/-- 概要：coslice の curry の射影は元の join からの射の右制限。
方針：Yoneda の同値の単射性と右包含の自然性を使う。
規約：任意の A に対して成り立ち、quasicategory の仮定は不要。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の射影の持ち上げ問題。 -/
lemma sliceUnderCurry_projection {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A ≫ F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (stdSimplex.obj n.unop) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm a) ≫ F)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A ≫ F).app n a
  apply SSet.yonedaEquiv.symm.injective
  rw [Equiv.symm_apply_apply, ← SSet.yonedaEquiv_symm_comp,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc]

/-- 概要：coslice への射を uncurry した錐の右制限は射影との合成。
方針：普遍性の逆関係を curry の射影の式に適用する。
規約：任意の A に対して成り立つ。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の射影の持ち上げ問題。 -/
lemma sliceUnderUncurry_projection {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  have h := sliceUnderCurry_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed f)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry_uncurry] at h
  exact h.symm

/-- 概要：quasicategory の coslice 射影は left anodyne な部分複体包含に対し持ち上げ性を持つ。
方針：錐と射影の値を空部分複体との pushout-join 上で貼り合わせ、内 anodyne 性で延長する。
規約：図式 K→X と試験する部分複体 A₀⊆A は任意。
使われ方：HTT Proposition 2.1.2.2、Kerodon §4.3.6（Tag 018E） の左ファイブレーション性。 -/
lemma sliceUnderProjection_hasLiftingProperty {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions A₀.ι) :
    HasLiftingProperty A₀.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) := by
  constructor
  intro a b sq
  let E : SSet.{u} := (⊥ : K.Subcomplex)
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry a
  let H := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K A).hom ≫ b
  have hover : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (⊥ : K.Subcomplex).ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 E) A₀.ι ≫ H := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K (A₀ : SSet.{u})).inv).1
    rw [← Category.assoc, emptyJoinIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (A₀ : SSet.{u}) ≫ G =
      A₀.ι ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K A).inv ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K A).hom ≫ b))
    rw [Iso.inv_hom_id_assoc, sliceUnderUncurry_projection]
    exact sq.w
  let hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout (⊥ : K.Subcomplex) A₀).flip
  let T := hs.desc G H hover
  have hT : CommSq T (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (⊥ : K.Subcomplex) A₀).ι (terminal.from X)
      (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A)) := ⟨terminal.hom_ext _ _⟩
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_leftAnodyne (⊥ : K.Subcomplex) A₀ hA
    (terminal.from X) InnerFibration.mem
  let L := hT.lift
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι, Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (⊥ : K.Subcomplex) A₀ ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (⊥ : K.Subcomplex) A₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inl_desc G H hover
  have hright : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (⊥ : K.Subcomplex).ι (𝟙 A) ≫ L = H := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι, Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (⊥ : K.Subcomplex) A₀ ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (⊥ : K.Subcomplex) A₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inr_desc G H hover
  have hfixed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ L = p := by
    have hh := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (A₀ : SSet.{u}) ≫ z) hleft
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective p
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    exact hleft
  · rw [sliceUnderCurry_projection]
    have hh := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso K A).inv ≫ z) hright
    rw [← Category.assoc, emptyJoinIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp] at hh
    exact hh.trans (by dsimp [H]; rw [← emptyJoinIso_inv, Iso.inv_hom_id_assoc])

/-- 概要：quasicategory の任意の図式上の coslice 射影は左ファイブレーション。
方針：左ホーン包含の left anodyne 性と射影の持ち上げ補題を使う。
規約：K の有限性等の追加仮定はない。
使われ方：HTT Proposition 2.1.2.2、Kerodon §4.3.6（Tag 018E） の coslice の一般論。 -/
@[kerodon 018F, kerodon 020U]
instance sliceUnderProjection_leftFibration {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hn =>
      exact sliceUnderProjection_hasLiftingProperty p _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_horn i hn)

/-- 概要：quasicategory の任意の図式上の coslice は quasicategory。
方針：射影は左ファイブレーション、従って inner fibration である。
規約：Mathlib の quasicategory_of_innerFibration を適用する。
使われ方：HTT Proposition 2.1.2.2、余極限を coslice の始対象として定義する基盤。 -/
@[kerodon 020U]
instance sliceUnder_quasicategory {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
