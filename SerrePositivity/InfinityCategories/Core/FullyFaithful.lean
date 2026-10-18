module

public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.TerminalTransport

/-!
概要：写像空間による充満忠実性と本質的全射性。
方針：右 pinched 写像空間のホモトピー同値を定義し、π₀ をホモトピー圏の Hom に移す。
規約：ホモトピー圏の充満忠実性だけを定義にはしない。
使われ方：HTT §2.2、Kerodon §4.8.3、Theorem 4.8.4.1。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像空間による充満忠実性。
方針：各右 pinched 写像空間の射が単体的ホモトピー逆を持つことを要求する。
規約：quasicategory 性は利用する定理に仮定する。
使われ方：Kerodon Remark 4.8.3.9、Theorem 4.8.4.1。 -/
def IsFullyFaithful {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x y : X _⦋0⦌, IsSimplicialHomotopyEquivalence (pinchedHomMap f x y)

/-- 概要：ホモトピー圏の頂点の同型による本質的全射性。
方針：任意の標的の頂点が像の頂点と同型であることを要求する。
規約：頂点の等号を要求しない。
使われ方：Kerodon Definition 4.8.1.1、Theorem 4.8.4.1。 -/
def IsEssentiallySurjective {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ y : Y _⦋0⦌, ∃ x : X _⦋0⦌, Nonempty (VertexIso (f.app (Opposite.op ⦋0⦌) x) y)

/-- 概要：恒等射は写像空間の意味で充満忠実。
方針：写像空間への恒等作用と恒等射のホモトピー同値性を使う。
規約：任意の単体集合。
使われ方：Kerodon §4.8.3 の基本例。 -/
lemma isFullyFaithful_id (X : SSet.{u}) : IsFullyFaithful (𝟙 X) := by
  intro x y
  rw [pinchedHomMap_id]
  exact isSimplicialHomotopyEquivalence_id _

/-- 概要：恒等射は本質的全射。
方針：同じ頂点と恒等同型を取る。
規約：任意の単体集合。
使われ方：Kerodon §4.8.1 の基本例。 -/
lemma isEssentiallySurjective_id (X : SSet.{u}) : IsEssentiallySurjective (𝟙 X) :=
  fun x ↦ ⟨x, ⟨Iso.refl _⟩⟩

/-- 概要：写像空間で充満忠実な射はホモトピー圏の各 Hom の全単射を誘導する。
方針：写像空間の π₀ の全単射を自然な Hom の同値で移す。
規約：X と Y は quasicategory。
使われ方：Kerodon §4.8.3 の充満忠実性の通常の圏への帰結。 -/
lemma IsFullyFaithful.homotopyCategoryMap_bijective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f)
    (x y : X _⦋0⦌) : Function.Bijective
      ((hoFunctor.map f).toFunctor.map :
        (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) →
        (SSet.HomotopyCategory.mk (f.app (Opposite.op ⦋0⦌) x) ⟶
          SSet.HomotopyCategory.mk (f.app (Opposite.op ⦋0⦌) y))) := by
  let eX := pinchedHomPiZeroEquiv x y
  let eY := pinchedHomPiZeroEquiv (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
  let eπ := Equiv.ofBijective (SSet.mapπ₀ (pinchedHomMap f x y)) (hf x y).mapPiZero_bijective
  let e := eX.symm.trans (eπ.trans eY)
  have he (a : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
      e a = (hoFunctor.map f).toFunctor.map a := by
    have h := pinchedHomPiZeroToHom_naturality f x y (eX.symm a)
    change e a = (hoFunctor.map f).toFunctor.map (eX (eX.symm a)) at h
    simpa only [Equiv.apply_symm_apply] using h
  constructor
  · intro a b hab
    exact e.injective ((he a).trans (hab.trans (he b).symm))
  · intro b
    obtain ⟨a, ha⟩ := e.surjective b
    exact ⟨a, (he a).symm.trans ha⟩

/-- 概要：写像空間で充満忠実な射はホモトピー圏の充満忠実な関手を与える。
方針：任意の対象を頂点で表し、各 Hom の全単射から逆写像を選ぶ。
規約：これは quasicategory の逆射を構成する主張とは別の帰結。
使われ方：Kerodon §4.8.3、Theorem 4.8.4.1 の準備。 -/
noncomputable def IsFullyFaithful.toHoFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f) :
    (hoFunctor.map f).toFunctor.FullyFaithful := by
  have hb (a b : hoFunctor.obj X) : Function.Bijective
      ((hoFunctor.map f).toFunctor.map : (a ⟶ b) → _) := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    exact hf.homotopyCategoryMap_bijective x y
  have : (hoFunctor.map f).toFunctor.Full := ⟨fun {a b} ↦ (hb a b).2⟩
  have : (hoFunctor.map f).toFunctor.Faithful := ⟨fun {a b} ↦ (hb a b).1⟩
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- 概要：本質的全射性はホモトピー圏の関手の本質的全射性と同値。
方針：両ホモトピー圏の対象を頂点として表す。
規約：この同値自体には quasicategory 性を必要としない。
使われ方：Kerodon Remark 4.8.1.3。 -/
lemma isEssentiallySurjective_iff_hoFunctor {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsEssentiallySurjective f ↔ (hoFunctor.map f).toFunctor.EssSurj := by
  constructor
  · intro hf
    constructor
    intro y
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨SSet.HomotopyCategory.mk x, hx⟩
  · intro hf y
    obtain ⟨x, hx⟩ := hf.mem_essImage (SSet.HomotopyCategory.mk y)
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    exact ⟨x, hx⟩

/-- 概要：quasicategory の同値は本質的全射。
方針：A3a のホモトピー圏の圏同値から本質的全射性を得る。
規約：同値の順方向の射についての主張。
使われ方：Kerodon §4.8.1 の同値の基本性質。 -/
lemma QCatEquivalence.isEssentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    IsEssentiallySurjective e.hom := by
  apply (isEssentiallySurjective_iff_hoFunctor e.hom).2
  change e.toHoEquivalence.functor.EssSurj
  infer_instance

/-- 概要：本質的全射な射の合成は本質的全射。
方針：二段階で像の頂点を選び、同型を関手で写して合成する。
規約：quasicategory 性は不要。
使われ方：Kerodon Remark 4.8.1.7。 -/
lemma IsEssentiallySurjective.comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsEssentiallySurjective f) (hg : IsEssentiallySurjective g) :
    IsEssentiallySurjective (f ≫ g) := by
  intro z
  obtain ⟨y, ⟨ey⟩⟩ := hg z
  obtain ⟨x, ⟨ex⟩⟩ := hf y
  exact ⟨x, ⟨VertexIso.map ex g ≪≫ ey⟩⟩

/-- 概要：充満忠実かつ本質的全射な射はホモトピー圏の圏同値を与える。
方針：ホモトピー圏で得た充満忠実性と本質的全射性を使う。
規約：この段階では quasicategory の逆射の構成は主張しない。
使われ方：Kerodon Theorem 4.8.4.1 の必要な通常の圏の帰結。 -/
noncomputable def IsFullyFaithful.toHoEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y}
    (hf : IsFullyFaithful f) (he : IsEssentiallySurjective f) :
    hoFunctor.obj X ≌ hoFunctor.obj Y := by
  have := hf.toHoFullyFaithful.full
  have := hf.toHoFullyFaithful.faithful
  have := (isEssentiallySurjective_iff_hoFunctor f).1 he
  have : (hoFunctor.map f).toFunctor.IsEquivalence := {}
  exact (hoFunctor.map f).toFunctor.asEquivalence

/-- 概要：関手単体集合での同型は各頂点でホモトピー圏の同型を与える。
方針：A3a の自然同型の頂点での成分を取る。
規約：両単体集合を quasicategory とする。
使われ方：Kerodon §4.5.1、§4.8.1 の関手の同型の成分。 -/
noncomputable def FunctorIso.app {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (x : X _⦋0⦌) :
    VertexIso (f.app (Opposite.op ⦋0⦌) x) (g.app (Opposite.op ⦋0⦌) x) :=
  e.toNatIso.app (SSet.HomotopyCategory.mk x)

end SerrePositivity.InfinityCategories
