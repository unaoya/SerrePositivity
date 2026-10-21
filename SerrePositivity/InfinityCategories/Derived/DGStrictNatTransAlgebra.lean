module
public import SerrePositivity.InfinityCategories.DGNerve.NatTrans
/-!
概要：厳密 dg 自然変換の恒等・合成と、その左右単位律・結合律を全斉次射上で証明する。
方針：閉零成分の通常順合成、Leibniz 則、元の全 Hom 自然性を使う。
規約：成分だけの通常自然性で代用しない。使われ方：元の nerve 比較の合成二単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} {E : Type w}
  [DGCategory R C] [DGCategory R E]
/-- 同じ dg 関手の厳密 dg 恒等自然変換。 -/
def dgStrictNatTransId (F : DGFunctor R C E) : StrictNatTrans F F where
  app x := unitElement R (F.obj x)
  naturality f := (unit_compose R ((F.map _ _).f _ f)).trans
    (compose_unit R ((F.map _ _).f _ f)).symm
/-- 元の二つの厳密 dg 自然変換の、閉零成分の通常順合成。 -/
def dgStrictNatTransComp {F G H : DGFunctor R C E}
    (η : StrictNatTrans F G) (θ : StrictNatTrans G H) : StrictNatTrans F H where
  app x := ⟨compose R (θ.app x).val (η.app x).val (zero_add 0), by
    change differential R (compose R (θ.app x).val (η.app x).val (zero_add 0)) = 0
    have hθ : differential R (θ.app x).val = 0 := (θ.app x).property
    have hη : differential R (η.app x).val = 0 := (η.app x).property
    rw [differential_compose]
    simp only [hθ, hη, zero_compose, compose_zero,
      smul_zero, zero_add]⟩
  naturality {x y k} f := by
    change compose R (compose R (θ.app y).val (η.app y).val (zero_add 0))
      ((F.map x y).f k f) (add_zero k) =
      compose R ((H.map x y).f k f)
        (compose R (θ.app x).val (η.app x).val (zero_add 0)) (zero_add k)
    calc
      _ = compose R (θ.app y).val
          (compose R (η.app y).val ((F.map x y).f k f) (add_zero k)) (add_zero k) :=
        (compose_assoc_of_sum _ _ _ (add_zero k) (zero_add 0) (add_zero k)).symm
      _ = compose R (θ.app y).val
          (compose R ((G.map x y).f k f) (η.app x).val (zero_add k)) (add_zero k) := by
        rw [η.naturality f]
      _ = compose R (compose R (θ.app y).val ((G.map x y).f k f) (add_zero k))
          (η.app x).val (zero_add k) :=
        compose_assoc_of_sum _ _ _ (zero_add k) (add_zero k) (add_zero k)
      _ = compose R (compose R ((H.map x y).f k f) (θ.app x).val (zero_add k))
          (η.app x).val (zero_add k) := by rw [θ.naturality]
      _ = _ := (compose_assoc_of_sum _ _ _ (zero_add 0) (zero_add k) (zero_add k)).symm
end SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} {E : Type w}
  [DGCategory R C] [DGCategory R E]
/-- 厳密 dg 自然変換は同じ閉零成分で決まる。 -/
lemma dgStrictNatTrans_ext {F G : DGFunctor R C E} {η θ : StrictNatTrans F G}
    (h : ∀ x, η.app x = θ.app x) : η = θ := by
  cases η with
  | mk a ha =>
    cases θ with
    | mk b hb =>
      have hab : a = b := funext h
      cases hab
      rfl
/-- 厳密 dg 自然変換の合成の左単位律。 -/
lemma dgStrictNatTransComp_id_left {F G : DGFunctor R C E} (η : StrictNatTrans F G) :
    dgStrictNatTransComp (dgStrictNatTransId F) η = η := by
  apply dgStrictNatTrans_ext
  intro x
  apply Subtype.ext
  exact compose_unit R (η.app x).val
/-- 厳密 dg 自然変換の合成の右単位律。 -/
lemma dgStrictNatTransComp_id_right {F G : DGFunctor R C E} (η : StrictNatTrans F G) :
    dgStrictNatTransComp η (dgStrictNatTransId G) = η := by
  apply dgStrictNatTrans_ext
  intro x
  apply Subtype.ext
  exact unit_compose R (η.app x).val
/-- 同じ厳密 dg 自然変換の三重合成は結合的。 -/
lemma dgStrictNatTransComp_assoc {F G H K : DGFunctor R C E}
    (η : StrictNatTrans F G) (θ : StrictNatTrans G H) (κ : StrictNatTrans H K) :
    dgStrictNatTransComp (dgStrictNatTransComp η θ) κ =
      dgStrictNatTransComp η (dgStrictNatTransComp θ κ) := by
  apply dgStrictNatTrans_ext
  intro x
  apply Subtype.ext
  exact compose_assoc_of_sum (η.app x).val (θ.app x).val (κ.app x).val
    (zero_add 0) (zero_add 0) (zero_add 0)
end SerrePositivity.InfinityCategories
