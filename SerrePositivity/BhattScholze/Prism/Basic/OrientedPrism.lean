module

public import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular

/-!
# 向き付き prism の定義と射（BS 著者版 Lemma 3.1・Def 3.2・Ex 3.3・Lemma 3.8）

## 概要
単項イデアル (d) を持つ prism とその射。p ∈ (d, φ(d)) と distinguished 性の同値（Lemma 3.1 の単項の場合）、
prism の p と d は Jacobson 根基に属し生成元は distinguished であること、射でイデアルの像が標的のイデアル全体になること、
結晶 prism（Ex 3.3）、完全 prism の台環は p 進完備で商のねじれは p で消えること（Lemma 3.8）。

## 方針
導来完備性は共通基盤の IsModuleComplete で述べる。導来 a 完備な環では a が Jacobson 根基に属する
（`DerivedCompletion.mem_jacobson_bot_of_isModuleComplete`）ので、生成元の distinguished 性と射の剛性は
p 正則性・完全性・有界性を仮定せずに Lemma 2.24・2.25 から出る。

## 規約
一般の局所単項なイデアルは扱わない（ノート D5）。

## 使われ方
BS のすべての prism の議論の土台。射の剛性の続き（I ⊗ B ≅ J、商による同型判定）は `Prism/Basic/Rigidity`。
-/

universe u v w t

/-! ## 主イデアルを持つ δ-pair の代数的条件（Lemma 3.1 の単項の場合、Lemma 3.5 の局所計算）

distinguished 生成元について必要なイデアルの包含と、δ 射によるイデアルの像を計算する。
prism の導来完備性はここでは使わない。
-/

@[expose] public noncomputable section OrientedDeltaPair

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- distinguished元dについてp∈(d^p,φ(d))。φ(d)-d^p=pδ(d)とδ(d)の逆元を使う。
Lemma 3.1の主イデアルの場合の強い包含で、完備性・根基の仮定は不要。 -/
theorem IsDistinguished.p_mem_span_pow {D : DeltaStructure p A} {d : A}
    (hd : D.IsDistinguished d) : (p : A) ∈ Ideal.span {d ^ p, D.frobeniusLift d} := by
  let I := Ideal.span {d ^ p, D.frobeniusLift d}
  have hdp : d ^ p ∈ I := Ideal.subset_span (by simp)
  have hφ : D.frobeniusLift d ∈ I := Ideal.subset_span (by simp)
  have hm : (p : A) * D.delta d ∈ I := by
    have h := I.sub_mem hφ hdp
    simpa only [D.frobeniusLift_apply, add_sub_cancel_left] using h
  obtain ⟨u, hu⟩ := hd
  have h := I.mul_mem_right (↑(u⁻¹) : A) hm
  rw [← hu, mul_assoc, Units.mul_inv, mul_one] at h
  exact h

/-- d,pがJacobson根基に属せば、distinguished性はp∈(d^p,φ(d))と同値。
弱い包含の判定Lemma 2.25と、主イデアルの強い包含を組み合わせる。 -/
theorem isDistinguished_iff_p_mem_span_pow (D : DeltaStructure p A) (d : A)
    (hdr : d ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    D.IsDistinguished d ↔ (p : A) ∈ Ideal.span {d ^ p, D.frobeniusLift d} := by
  refine ⟨fun h ↦ h.p_mem_span_pow, fun h ↦ ?_⟩
  apply D.isDistinguished_of_p_mem_span d hdr hpr
  apply (show Ideal.span {d ^ p, D.frobeniusLift d} ≤
      Ideal.span {d, D.frobeniusLift d} from ?_) h
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact (Ideal.span {d, D.frobeniusLift d}).pow_mem_of_mem
      (Ideal.subset_span (by simp)) p (Fact.out : p.Prime).pos
  · rw [Set.mem_singleton_iff.mp hx]
    exact Ideal.subset_span (by simp)

/-- δ射がdistinguished元dを(e)の中へ送り、e,pが終域のJacobson根基に属せば、d=e·rのrは単元。
Lemma 2.24をd=e·rに当てる。Lemma 3.5の局所的な計算。 -/
theorem IsDeltaHom.exists_isUnit_of_distinguished_of_mem_span
    {B : Type v} [CommRing B] {D : DeltaStructure p A} {E : DeltaStructure p B}
    {f : A →+* B} (hf : D.IsDeltaHom E f) {d : A} {e : B}
    (hd : D.IsDistinguished d) (he : f d ∈ Ideal.span {e})
    (her : e ∈ Ideal.jacobson (⊥ : Ideal B))
    (hpr : (p : B) ∈ Ideal.jacobson (⊥ : Ideal B)) :
    ∃ r : B, IsUnit r ∧ f d = e * r := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp he
  have hfd := hf.map_isDistinguished hd
  rw [hr] at hfd
  exact ⟨r, (E.isDistinguished_factor e r hfd her hpr).2, hr⟩

/-- δ射がdistinguished生成元dを(e)へ送れば、その主イデアルの像は(e)全体。
e,pが終域のJacobson根基に属する仮定で因子判定を使う。
Lemma 3.5の局所的な計算であり、一般prismの降下までは含まない。 -/
theorem IsDeltaHom.map_span_eq_of_distinguished_of_mem_span
    {B : Type v} [CommRing B] {D : DeltaStructure p A} {E : DeltaStructure p B}
    {f : A →+* B} (hf : D.IsDeltaHom E f) {d : A} {e : B}
    (hd : D.IsDistinguished d) (he : f d ∈ Ideal.span {e})
    (her : e ∈ Ideal.jacobson (⊥ : Ideal B))
    (hpr : (p : B) ∈ Ideal.jacobson (⊥ : Ideal B)) :
    (Ideal.span {d}).map f = Ideal.span {e} := by
  obtain ⟨r, hru, hr⟩ := hf.exists_isUnit_of_distinguished_of_mem_span hd he her hpr
  rw [Ideal.map_span, Set.image_singleton, hr, Ideal.span_singleton_mul_right_unit hru]

end SerrePositivity.BhattScholze.DeltaStructure

end OrientedDeltaPair

/-! ## 非零因子の生成元を選択した prism（Def 3.2 の単項の場合）

Cartier イデアルは (d) とし、導来 (p,d) 完備性は p と d それぞれの導来完備性で述べる。
導来完備性から p と d は Jacobson 根基に属するので、生成元はいつも distinguished。
-/

@[expose] public noncomputable section OrientedPrism

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]

/-- oriented prism：δ環、正則な生成元、導来(p,d)完備性、prismのイデアル条件。
生成元以外のCartierイデアルはこの型の対象外。 -/
structure OrientedPrism where
  deltaStructure : DeltaStructure p A
  generator : A
  generator_regular : Function.Injective (fun x : A ↦ generator * x)
  complete_p : DerivedCompletion.IsModuleComplete A (p : A) (ModuleCat.of A A)
  complete_generator : DerivedCompletion.IsModuleComplete A generator (ModuleCat.of A A)
  p_mem : (p : A) ∈ Ideal.span {generator, deltaStructure.frobeniusLift generator}

namespace OrientedPrism
variable {p A}

/-- 選択生成元の主イデアル。 -/
def ideal (P : OrientedPrism p A) : Ideal A := Ideal.span {P.generator}

/-- 選択生成元の主イデアルは有限生成。 -/
theorem ideal_fg (P : OrientedPrism p A) : P.ideal.FG :=
  Submodule.fg_span (Set.toFinite _)

/-- 原典のp∈I+φ(I)Aを選択した主イデアルについて満たす。 -/
theorem p_mem_sup_map (P : OrientedPrism p A) :
    (p : A) ∈ P.ideal ⊔ P.ideal.map P.deltaStructure.frobeniusLift := by
  simpa only [ideal, Ideal.map_span, Set.image_singleton, ← Ideal.span_union,
    Set.singleton_union] using P.p_mem

/-- distinguishedな正則元と実導来完備性からoriented prismを構成する。 -/
def ofDistinguished (D : DeltaStructure p A) (d : A)
    (hd : D.IsDistinguished d) (hreg : Function.Injective (fun x : A ↦ d * x))
    (hp : DerivedCompletion.IsModuleComplete A (p : A) (ModuleCat.of A A))
    (hc : DerivedCompletion.IsModuleComplete A d (ModuleCat.of A A)) : OrientedPrism p A :=
  ⟨D, d, hreg, hp, hc, hd.p_mem_span⟩

/-- 非零因子の生成元に関して、導来完備性から古典的完備性を得る。 -/
theorem isAdicComplete_generator (P : OrientedPrism p A) :
    IsAdicComplete (Ideal.span {P.generator}) A :=
  (DerivedCompletion.isModuleComplete_iff_isAdicComplete_of_regular A P.generator
    (ModuleCat.of A A) P.generator_regular).mp P.complete_generator

/-- pが正則なら、prismの導来p完備性から古典的p完備性を得る。 -/
theorem isAdicComplete_p_of_regular (P : OrientedPrism p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    IsAdicComplete (Ideal.span {(p : A)}) A :=
  (DerivedCompletion.isRingModuleComplete_iff_isAdicComplete_natCast A p hp).mp P.complete_p

/-- prismの導来p完備性から、pはJacobson根基に属する。 -/
theorem p_mem_jacobson (P : OrientedPrism p A) : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A) :=
  DerivedCompletion.mem_jacobson_bot_of_isModuleComplete A (p : A) P.complete_p

/-- prismの導来d完備性から、選択生成元はJacobson根基に属する。 -/
theorem generator_mem_jacobson (P : OrientedPrism p A) :
    P.generator ∈ Ideal.jacobson (⊥ : Ideal A) :=
  DerivedCompletion.mem_jacobson_bot_of_isModuleComplete A P.generator P.complete_generator

/-- oriented prismの選択生成元はdistinguished。p,dがJacobson根基に属するので、
Lemma 2.25をp∈(d,φ(d))に当てる。p正則性・完全性は要らない。 -/
theorem isDistinguished_generator (P : OrientedPrism p A) :
    P.deltaStructure.IsDistinguished P.generator :=
  P.deltaStructure.isDistinguished_of_p_mem_span P.generator
    P.generator_mem_jacobson P.p_mem_jacobson P.p_mem

/-- δ射が源の生成元を終域のイデアルへ送れば、イデアルの像は終域のイデアル全体。
Lemma 3.5の単項の場合。 -/
theorem map_ideal_eq_of_isDeltaHom {B : Type v} [CommRing B]
    (P : OrientedPrism p A) (Q : OrientedPrism p B)
    (f : A →+* B) (hf : P.deltaStructure.IsDeltaHom Q.deltaStructure f)
    (hI : f P.generator ∈ Q.ideal) : P.ideal.map f = Q.ideal :=
  hf.map_span_eq_of_distinguished_of_mem_span P.isDistinguished_generator hI
    Q.generator_mem_jacobson Q.p_mem_jacobson

end OrientedPrism
end SerrePositivity.BhattScholze

end OrientedPrism

/-! ## oriented prism の射と標準商への誘導（Def 3.2 の射）

δ-pair の射を主イデアルの場合に束ねる。選択した生成元そのものの保存は要求せず、
イデアルの保存を要求する。標準商上の射は Mathlib の quotientMap を再利用する。
-/

@[expose] public noncomputable section OrientedPrismHom

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

/-- prism射ではイデアルの像が終域のイデアル全体。Lemma 3.5の単項の場合（IB = J）。 -/
theorem map_ideal_eq (f : Hom P Q) : P.ideal.map f.toRingHom = Q.ideal :=
  P.map_ideal_eq_of_isDeltaHom Q f.toRingHom f.map_delta f.map_generator_mem

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

/-- 台の環射が全射なら、標準商への誘導射も全射。 -/
theorem quotientMap_surjective (f : Hom P Q) (hf : Function.Surjective f.toRingHom) :
    Function.Surjective f.quotientMap := by
  exact Ideal.quotientMap_surjective hf

end Hom
end SerrePositivity.BhattScholze.OrientedPrism

end OrientedPrismHom

/-! ## p を生成元に持つ結晶 oriented prism（Ex 3.3）

p 正則・古典的 p 進完備な δ 環から実導来条件を持つ結晶 prism を構成し、逆方向も共通比較で証明する。
-/

@[expose] public noncomputable section CrystallineOrientedPrism

namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p正則・p進完備なδ環に標準生成元pを持つ結晶oriented prismを付ける。 -/
def crystalline (D : DeltaStructure p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x))
    [IsAdicComplete (Ideal.span {(p : A)}) A] : OrientedPrism p A :=
  ofDistinguished D (p : A)
    (D.isDistinguished_p (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)})
      (Ideal.subset_span (by simp)))) hp
    (DerivedCompletion.isModuleComplete_of_isAdicComplete A (p : A) (ModuleCat.of A A))
    (DerivedCompletion.isModuleComplete_of_isAdicComplete A (p : A) (ModuleCat.of A A))

/-- 結晶構成のδ構造は元の構造。 -/
@[simp] theorem crystalline_deltaStructure (D : DeltaStructure p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x))
    [IsAdicComplete (Ideal.span {(p : A)}) A] : (crystalline D hp).deltaStructure = D := rfl

/-- 結晶構成の選択生成元はp。 -/
@[simp] theorem crystalline_generator (D : DeltaStructure p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x))
    [IsAdicComplete (Ideal.span {(p : A)}) A] : (crystalline D hp).generator = (p : A) := rfl

/-- 指定δ構造と生成元pを持つ結晶oriented prismの存在条件は、p正則・p進完備性。
Example 3.3の両方向を実導来完備性と古典的完備性の比較により証明する。 -/
theorem exists_crystalline_iff (D : DeltaStructure p A) :
    (∃ P : OrientedPrism p A, P.deltaStructure = D ∧ P.generator = (p : A)) ↔
      Function.Injective (fun x : A ↦ (p : A) * x) ∧ IsAdicComplete (Ideal.span {(p : A)}) A := by
  constructor
  · rintro ⟨P, _, hgen⟩
    have hp : Function.Injective (fun x : A ↦ (p : A) * x) := by
      simpa only [hgen] using P.generator_regular
    exact ⟨hp, P.isAdicComplete_p_of_regular hp⟩
  · rintro ⟨hp, hc⟩
    let := hc
    exact ⟨crystalline D hp, rfl, rfl⟩

end SerrePositivity.BhattScholze.OrientedPrism

end CrystallineOrientedPrism

/-! ## 完全 oriented prism（Lemma 3.8 の単項の場合）

完全 prism の台環は p 正則なので古典的 p 進完備、商の p 冪ねじれは p で消える（有界性の N = 1 の評価）。
生成元が distinguished であることは一般の `isDistinguished_generator` にある。
-/

@[expose] public noncomputable section PerfectOrientedPrism

namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全oriented prismの古典的p進完備性。 -/
theorem isAdicComplete_p_of_perfect (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) : IsAdicComplete (Ideal.span {(p : A)}) A :=
  P.isAdicComplete_p_of_regular hP.p_mul_injective

/-- 完全oriented prismの商のp冪ねじれはpで消える。
原典のbounded性の具体的な評価N=1。 -/
theorem quotient_p_pow_torsion_killed_by_p (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) (n : ℕ) (x : A ⧸ P.ideal)
    (hx : (p : A ⧸ P.ideal) ^ n * x = 0) : (p : A ⧸ P.ideal) * x = 0 :=
  hP.distinguished_quotient_p_pow_torsion_killed_by_p P.isDistinguished_generator n x hx

/-- p進・d進完備な完全δ環のdistinguished元は、実導来条件を持つoriented prismを与える。
古典的完備性から導来完備性への既存共通定理を明示的に使用する。 -/
def ofPerfectCompleteDistinguished (D : DeltaStructure p A) (hD : D.IsPerfect)
    (d : A) (hd : D.IsDistinguished d)
    [IsAdicComplete (Ideal.span {(p : A)}) A] [IsAdicComplete (Ideal.span {d}) A] :
    OrientedPrism p A :=
  ofDistinguished D d hd (hD.distinguished_mul_injective hd)
    (DerivedCompletion.isModuleComplete_of_isAdicComplete A (p : A) (ModuleCat.of A A))
    (DerivedCompletion.isModuleComplete_of_isAdicComplete A d (ModuleCat.of A A))

end SerrePositivity.BhattScholze.OrientedPrism

end PerfectOrientedPrism
