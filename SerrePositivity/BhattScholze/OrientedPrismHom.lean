module

public import SerrePositivity.BhattScholze.PerfectOrientedPrism

/-! # oriented prismの射と標準商への誘導

著者公開版Def 3.2のδ-pairの射を主イデアルの場合に束ねる。
選択した生成元そのものの保存は要求せず、イデアルの保存を要求する。
標準商上の射はMathlibのquotientMapを再利用する。
-/

@[expose] public noncomputable section
universe u v w t
namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} {B : Type v} {C : Type w} {D : Type t}
variable [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- δ構造とprismイデアルを保存する環射。選択したorientationの厳密な保存は不要。 -/
structure Hom (P : OrientedPrism p A) (Q : OrientedPrism p B) extends A →+* B where
  map_delta : P.deltaStructure.IsDeltaHom Q.deltaStructure toRingHom
  ideal_le : P.ideal ≤ Q.ideal.comap toRingHom

namespace Hom
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable {T : OrientedPrism p C} {U : OrientedPrism p D}

/-- prism射は台の環射で決まる。 -/
@[ext] theorem ext {f g : Hom P Q} (h : f.toRingHom = g.toRingHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- 恒等prism射。 -/
def id (P : OrientedPrism p A) : Hom P P :=
  ⟨RingHom.id A, P.deltaStructure.isDeltaHom_id, fun _ hx ↦ hx⟩

/-- prism射の合成。 -/
def comp (g : Hom Q T) (f : Hom P Q) : Hom P T :=
  ⟨g.toRingHom.comp f.toRingHom, g.map_delta.comp f.map_delta,
    fun _ hx ↦ g.ideal_le (f.ideal_le hx)⟩

/-- 恒等射との右合成。 -/
@[simp] theorem comp_id (f : Hom P Q) : f.comp (id P) = f := by
  apply ext
  exact RingHom.comp_id _

/-- 恒等射との左合成。 -/
@[simp] theorem id_comp (f : Hom P Q) : (id Q).comp f = f := by
  apply ext
  exact RingHom.id_comp _

/-- prism射の合成は結合的。 -/
theorem comp_assoc (h : Hom T U) (g : Hom Q T) (f : Hom P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext
  exact RingHom.comp_assoc _ _ _

/-- 源の選択生成元の像は終域のイデアルに属する。 -/
theorem map_generator_mem (f : Hom P Q) : f.toRingHom P.generator ∈ Q.ideal :=
  f.ideal_le (Ideal.subset_span (by simp))

/-- 標準商環への誘導射。商にはδ構造を付けない。 -/
def quotientMap (f : Hom P Q) : A ⧸ P.ideal →+* B ⧸ Q.ideal :=
  Ideal.quotientMap Q.ideal f.toRingHom f.ideal_le

/-- 誘導商射は代表元上で元の環射を適用する。 -/
@[simp] theorem quotientMap_mk (f : Hom P Q) (x : A) :
    f.quotientMap (Ideal.Quotient.mk P.ideal x) = Ideal.Quotient.mk Q.ideal (f.toRingHom x) := rfl

/-- 台環の標準商射との可換性。 -/
theorem quotientMap_comp_mk (f : Hom P Q) :
    f.quotientMap.comp (Ideal.Quotient.mk P.ideal) =
      (Ideal.Quotient.mk Q.ideal).comp f.toRingHom := rfl

/-- 恒等prism射からの商射は恒等射。 -/
@[simp] theorem quotientMap_id (P : OrientedPrism p A) :
    (id P).quotientMap = RingHom.id (A ⧸ P.ideal) := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- prism射の合成から誘導する商射は、各商射の合成に等しい。 -/
@[simp] theorem quotientMap_comp (g : Hom Q T) (f : Hom P Q) :
    (g.comp f).quotientMap = g.quotientMap.comp f.quotientMap := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- 完全oriented prismの射ではイデアルの像が終域のイデアル全体。 -/
theorem map_ideal_eq_of_perfect (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    P.ideal.map f.toRingHom = Q.ideal :=
  P.map_ideal_eq_of_perfect Q hP hQ f.toRingHom f.map_delta f.map_generator_mem

/-- 台の環射が全射なら、標準商への誘導射も全射。 -/
theorem quotientMap_surjective (f : Hom P Q) (hf : Function.Surjective f.toRingHom) :
    Function.Surjective f.quotientMap := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨Ideal.Quotient.mk P.ideal a, rfl⟩

end Hom
end SerrePositivity.BhattScholze.OrientedPrism
